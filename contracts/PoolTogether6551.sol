// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.0;

import "@openzeppelin/contracts/access/Ownable.sol";
import "@openzeppelin/contracts/security/ReentrancyGuard.sol";

import "@openzeppelin/contracts/interfaces/IERC721.sol";
import "@openzeppelin/contracts/token/ERC20/utils/SafeERC20.sol";
import "@openzeppelin/contracts/utils/Create2.sol";

import "@chainlink/contracts/src/v0.8/interfaces/VRFCoordinatorV2Interface.sol";
import "@chainlink/contracts/src/v0.8/VRFConsumerBaseV2.sol";

import "../interfaces/ILendingPool.sol";
import "../interfaces/ILendingPoolAddressesProvider.sol";
import "../interfaces/IERC6551Registry.sol";
import "../interfaces/IERC6551Account.sol";
import "../interfaces/IPUSHCommInterface.sol";
import "../interfaces/OptimisticOracleV3Interface.sol";

import "@openzeppelin/contracts/utils/Strings.sol";


bytes32 constant VRF_KEY_HASH = 0x8af398995b04c28e9951adb9721ef74c74f93e6a478f39e7e0777be13527e7ef;
uint32 constant VRF_CALLBACK_GAS = 150_000;
uint16 constant VRF_REQ_CONFIRM = 3;
uint32 constant VRF_NUM_WORDS = 1;


contract PoolTogether6551 is IERC6551Registry, VRFConsumerBaseV2, Ownable, ReentrancyGuard {
    using SafeERC20 for IERC20;
    using Strings for uint256;

    ///
    /// Structs

    struct Round {
        uint256 timestamp;
        uint256 randomnessReqId;
        uint256 prizeAmount;
        address winner;

        // weights
        uint256 totalRoundWeight;
        uint256[] userChances;
        bytes32 assertionId;
    }

    struct DepositTicket {
        address owner;
        uint256 deposit;
    }

    ///
    /// Enums.

    enum TicketOperation{ SET, SUB, ADD }

    ///
    /// Internal variables.

    uint64 internal _vrfSub;
    uint256 internal _minRoundDuration;
    uint256 internal _currentRoundStart;

    address internal immutable _dai;
    address internal immutable _usdc;
    address internal immutable _umaV3;
    address internal immutable _vrfCoordinator;
    address internal immutable _lendingPool;
    address internal immutable _pushPolygonAddress;
    address internal immutable _pushChannelCreator;

    // The current round id.
    uint256 internal _roundId = 0;
    // Total deposit amount in AAVE pool.
    uint256 internal _totalDeposit = 0;

    // Internal array to store participant tickets.
    DepositTicket[] internal _tickets;
    // Internal map to find ticket index from user address.
    mapping(address => uint256) internal _userToTicketId;

    // Internal map to find round id from randomness request id.
    mapping(uint256 => uint256) internal _reqIdToRoundId;
    // Public map to find round details from round id.
    mapping(uint256 => Round) public finishedRounds;

    // Internal map to find accounts.
    // @dev 1 NFT token id should have only 1 account.
    mapping(bytes32 => bool) public accountCreated;

    ///
    /// The errors.

    error InitializationFailed();
    error TicketNotFound();
    error InvalidTicketOperation();
    error RoundNotFound();
    error InsufficientPrize();
    error EmptyRound();
    error RoundNotFinished();
    error InvalidWeights();
    error InvalidNFTOwner();
    error InvalidAmount();
    error InvalidChain();
    error AccountAlreadyCreated();
    error AccountNotFound();
    error WinnerNotFound();

    ///
    /// The contract constructor.

    constructor(
        uint64 vrfSub,
        uint256 minRoundDuration,
        address lendingPool,
        address vrfCoordinator,
        address dai,
        address usdc,
        address pushPolygonAddress,
        address pushChannelCreator,
        address umaV3
    ) VRFConsumerBaseV2(vrfCoordinator) {
        // Set round details.
        _minRoundDuration = minRoundDuration;
        _currentRoundStart = block.timestamp;

        // Ticket index zero is reserved for the address(this)
        // either the `user == address(this)` or the ticket simply doesn't exist.
        updateTicket(address(this), TicketOperation.SET, 0);

        // Set VRF subscription.
        _vrfSub = vrfSub;

        // Set addresses.
        _lendingPool = lendingPool;
        _vrfCoordinator = vrfCoordinator;
        _pushPolygonAddress = pushPolygonAddress;
        _pushChannelCreator = pushChannelCreator;
        _dai = dai;
        _usdc = usdc;
        _umaV3 = umaV3;

        // Approve USDC for UMA.
        IERC20(_usdc).approve(umaV3, type(uint256).max);

        // Start the first round.
        _roundId += 1;
    }

    ///
    /// Events

    event TicketUpdated(address indexed user, TicketOperation operation, uint256 amount);
    event RoundFinished(uint256 indexed roundId, uint256 randomnessReqId, uint256 prizeAmount);
    event WinnerSelected(uint256 indexed roundId, address winner);

    ///
    /// ERC6551 Registry

    function createAccount(
        address implementation,
        uint256 chainId,
        address tokenContract,
        uint256 tokenId,
        uint256 salt,
        bytes calldata initData
    ) external override returns (address) {
        bytes memory code = _creationCode(implementation, chainId, tokenContract, tokenId, salt);

        address _account = Create2.computeAddress(
            bytes32(salt),
            keccak256(code)
        );

        // Require 1 account for 1 NFT on same chain.
        bytes32 accountHash = getAccountHash(tokenContract, tokenId, chainId);
        if (accountCreated[accountHash])
            revert AccountAlreadyCreated();

        if (_account.code.length != 0) return _account;

        _account = Create2.deploy(0, bytes32(salt), code);

        if (initData.length != 0) {
            (bool success, ) = _account.call(initData);
            if (!success) revert InitializationFailed();
        }

        emit AccountCreated(
            _account,
            implementation,
            chainId,
            tokenContract,
            tokenId,
            salt
        );

        accountCreated[accountHash] = true;
        return _account;
    }

    ///
    /// The deposit and withdrawal functions.

    /// @dev Requires DAI approve from frontend.
    /// @dev Call with `executeCall` from 6551 account.
    function depositDAI(
        uint256 amount
    ) external nonReentrant check6551Account(_msgSender()) {
        // Gas savings.
        address dai = _dai;

        // Transfer ERC20 from 6551 account.
        uint beforeBalance = IERC20(dai).balanceOf(address(this));
        IERC20(dai).transferFrom(_msgSender(), address(this), amount);
        uint afterBalance = IERC20(dai).balanceOf(address(this));

        // Check transferred amounts.
        if (afterBalance - beforeBalance != amount)
            revert InvalidAmount();

        // Approve and deposit to AAVE.
        IERC20(dai).approve(_lendingPool, amount);
        ILendingPool(_lendingPool).deposit(dai, amount, address(this), 0);

        // Increase 6551 account deposit.
        updateTicket(_msgSender(), TicketOperation.ADD, amount);
        _totalDeposit += amount;
    }

    /// @dev Call with `executeCall` from 6551 account.
    function withdrawDAI(
        uint256 amount
    ) external nonReentrant check6551Account(_msgSender()) {
        // Get user ticket. (will revert if not found)
        DepositTicket memory userTicket = getUserTicket(_msgSender());

        // Check balance.
        if (amount != userTicket.deposit)
            revert InvalidAmount();

        // Withdraw from AAVE.
        ILendingPool(_lendingPool).withdraw(_dai, amount, userTicket.owner);

        // Decrease the 6551 account deposit.
        updateTicket(userTicket.owner, TicketOperation.SUB, amount);
        _totalDeposit -= amount;
    }

    ///
    /// Modifiers

    /// @dev Checks if the sender is an 6551 account.
    modifier check6551Account(address account6551) {
        // Get bounded token.
        (uint256 chainId, address tokenContract, uint256 tokenId) = IERC6551Account(payable(account6551)).token();

        // Check chain id.
        uint256 id;
        assembly {
            id := chainid()
        }

        if (id != chainId)
            revert InvalidChain();

        // Check account hash.
        bytes32 accountHash = getAccountHash(tokenContract, tokenId, chainId);
        if (!accountCreated[accountHash])
            revert AccountNotFound();

        _;
    }

    ///
    /// Owner only functions.

    /// @dev The `weights` should have the same order as the `_tickets`.
    /// @dev `useMockPrize` implementation should be removed at production.
    function finishRound(uint256 totalWeight, uint256[] memory weights, bool useMockPrize) external onlyOwner {
        // Check weights.
        if (weights.length > _tickets.length)
            revert InvalidWeights();

        // Check total deposit.
        if (_totalDeposit == 0)
            revert EmptyRound();

        // Check if round has finished.
        if (block.timestamp < (_minRoundDuration + _currentRoundStart))
            revert RoundNotFinished();

        // Check prize.
        uint256 prizeAmount = 0;
        (uint256 totalCollateral,,,,,) = ILendingPool(_lendingPool).getUserAccountData(address(this));
        if (totalCollateral <= _totalDeposit) {
            // Revert if not mocked.
            if (!useMockPrize) revert InsufficientPrize();

            // Mock prize amount to 1 DAI.
            prizeAmount = 1e16;
        } else {
            // Withdraw the earned amounts and unwrap.
            prizeAmount = ILendingPool(_lendingPool).withdraw(
                _dai,
                totalCollateral - _totalDeposit,
                address(this)
            );
        }

        // Get randomness from VRF.
        uint256 reqId;
        if (!useMockPrize) {
            reqId = VRFCoordinatorV2Interface(_vrfCoordinator).requestRandomWords(
                VRF_KEY_HASH,
                _vrfSub,
                VRF_REQ_CONFIRM,
                VRF_CALLBACK_GAS,
                VRF_NUM_WORDS
            );
        } else {
            reqId = 1;
        }

        // Add round details to the finished rounds.
        finishedRounds[_roundId] = Round(block.timestamp, reqId, prizeAmount,  address(0), totalWeight, weights, bytes32(0));
        _reqIdToRoundId[reqId] = _roundId;
        emit RoundFinished(_roundId, reqId, prizeAmount);

        // Increase the round.
        _roundId += 1;
        _currentRoundStart = block.timestamp;

        // Call mock function.
        if (useMockPrize) {
            uint256[] memory words = new uint256[](1);
            words[0] = 1e5;
            fulfillRandomWords(reqId, words);
        }
    }

    ///
    /// View functions.

    function account(
        address implementation,
        uint256 chainId,
        address tokenContract,
        uint256 tokenId,
        uint256 salt
    ) external view returns (address) {
        bytes32 bytecodeHash = keccak256(
            _creationCode(implementation, chainId, tokenContract, tokenId, salt)
        );

        return Create2.computeAddress(bytes32(salt), bytecodeHash);
    }

    /// @dev Use this to get the total deposit of an single user.
    /// @dev Reverts if the deposit is not found or zero.
    function getUserTicket(address user) public view returns (DepositTicket memory) {
        // Get the ticket index.
        uint256 ticketIndex = _userToTicketId[user];

        // Check index.
        if (ticketIndex == 0)
            revert TicketNotFound();

        return _tickets[ticketIndex];
    }

    /// @dev Use this to get user deposits in bulk.
    function getBulkTickets(uint256 start, uint256 stop) public view returns (DepositTicket[] memory tickets) {
        uint len = stop - start;
        tickets = new DepositTicket[](len);
        for (uint i = 0; i < len; i++) {
            tickets[i] = _tickets[start + i];
        }
    }

    /// @dev Use this to get total ticket count.
    function getTicketsCount() external view returns (uint256) {
        return _tickets.length;
    }

    /// @dev Use this to get active round id.
    function getActiveRoundId() external view returns (uint256) {
        return _roundId;
    }

    ///
    /// Internal functions.

    function getAccountHash(address tokenContract, uint256 tokenId, uint256 chainId) internal pure returns(bytes32) {
        return keccak256(
            abi.encodePacked(tokenContract, tokenId, chainId)
        );
    }

    function _creationCode(
        address implementation_,
        uint256 chainId_,
        address tokenContract_,
        uint256 tokenId_,
        uint256 salt_
    ) internal pure returns (bytes memory) {
        return
            abi.encodePacked(
            hex"3d60ad80600a3d3981f3363d3d373d3d3d363d73",
            implementation_,
            hex"5af43d82803e903d91602b57fd5bf3",
            abi.encode(salt_, chainId_, tokenContract_, tokenId_)
        );
    }

    function updateTicket(address user, TicketOperation op, uint256 amount) internal {
        // Get the ticket index.
        uint256 ticketIndex = _userToTicketId[user];

        // Create new ticket if doesn't exist.
        if (ticketIndex == 0) {
            // Create new ticket.
            DepositTicket memory ticket = DepositTicket(user, amount);
            _userToTicketId[user] = _tickets.length;
            _tickets.push(ticket);

            // Set new ticket index.
            ticketIndex = _tickets.length - 1;
        }

        // Update the existing ticket.
        else if (op == TicketOperation.ADD) _tickets[ticketIndex].deposit += amount;
        else if (op == TicketOperation.SUB) _tickets[ticketIndex].deposit -= amount;
        else if (op == TicketOperation.SET) _tickets[ticketIndex].deposit = amount;
        else revert InvalidTicketOperation();

        // Emit event.
        emit TicketUpdated(user, op, amount);
    }

    function fulfillRandomWords(uint256 requestId, uint256[] memory randomWords) internal override {
        // Get round id.
        uint256 roundId = _reqIdToRoundId[requestId];
        if (roundId == 0)
            revert RoundNotFound();

        // Get round details.
        Round memory round = finishedRounds[roundId];

        // Generate a random number within the total weight range.
        uint256 winnerWeight = randomWords[0] % (round.totalRoundWeight);

        uint cumulativeWeight;
        address winner;

        // Iterate over and select a winner.
        for (uint i = 1; i < round.userChances.length ; i++) {
            cumulativeWeight += round.userChances[i];

            if (cumulativeWeight >= winnerWeight) {
                winner = _tickets[i].owner;
                break;
            }
        }

        // Check winner.
        if (winner == address(0))
            revert WinnerNotFound();

        // Transfer prize.
        IERC20(_dai).transfer(winner, round.prizeAmount);

        // Emit winner selected.
        finishedRounds[roundId].winner = winner;
        emit WinnerSelected(roundId, winner);

        IPUSHCommInterface(_pushPolygonAddress).sendNotification(
            _pushChannelCreator, // from channel,
            address(this), // to recipient, put address(this) in case you want Broadcast or Subset. For Targetted put the address to which you want to send
            bytes(
                string(
                    // We are passing identity here: https://docs.epns.io/developers/developer-guides/sending-notifications/advanced/notification-payload-types/identity/payload-identity-implementations
                    abi.encodePacked(
                        "0", // this is notification identity: https://docs.epns.io/developers/developer-guides/sending-notifications/advanced/notification-payload-types/identity/payload-identity-implementations
                        "+", // segregator
                        "1", // this is payload type: https://docs.epns.io/developers/developer-guides/sending-notifications/advanced/notification-payload-types/payload (1, 3 or 4) = (Broadcast, targetted or subset)
                        "+", // segregator
                        "Today's winner is chosen! Come check it!"
                    )
                )
            )
        );

        // UMA.
        assertUMA(roundId, winner);
    }

    // @dev Mocked fulfill random words callback.
    // @dev Should be removed at production.
    function mockFulfillRandomWords(uint256 requestId, uint256[] memory randomWords) external onlyOwner  {
        fulfillRandomWords(requestId, randomWords);
    }

    ///
    /// UMA V3

    function assertUMA(uint256 roundId, address winner) internal {
        // Check USDC balance for UMA.
        OptimisticOracleV3Interface oracle = OptimisticOracleV3Interface(_umaV3);
        uint256 minThreshold = oracle.getMinimumBond(_usdc);
        uint256 balance = IERC20(_usdc).balanceOf(address(this));

        // Skip if we don't have enough balance.
        if (minThreshold > balance) return;

        // Assert truth if balance is ok.
        finishedRounds[_roundId].assertionId = oracle.assertTruthWithDefaults(
            bytes(abi.encodePacked(
                "Round: ",
                roundId,
                " Winner: ",
                winner
            )),
            address(this)
        );
    }

    function settleAndGetAssertionResult(uint _round) public returns (bool) {
        return OptimisticOracleV3Interface(_umaV3)
            .settleAndGetAssertionResult(finishedRounds[_round].assertionId);
    }

    function getAssertionResult(uint _round) public view returns (bool) {
        return OptimisticOracleV3Interface(_umaV3)
            .getAssertionResult(finishedRounds[_round].assertionId);
    }

    function getAssertion(uint _round)
        public
        view
        returns (OptimisticOracleV3Interface.Assertion memory)
    {
        return OptimisticOracleV3Interface(_umaV3)
            .getAssertion(finishedRounds[_round].assertionId);
    }
}