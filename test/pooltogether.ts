import { ethers } from "hardhat";
import { expect } from "chai";
import {BigNumber, Signer} from "ethers";
import {
    PoolTogether6551,
    PoolTogether6551__factory,
    VRFCoordinatorV2Mock,
    VRFCoordinatorV2Mock__factory,
    PoolAccount6551,
    PoolAccount6551__factory, MockERC721__factory, MockERC721, IERC20__factory
} from "../typechain-types";

const USDC = "0x2791bca1f2de4661ed88a30c99a7a9449aa84174";
    const AAVE = "0x8dff5e27ea6b7ac08ebfdf9eb090f32ee9a30fcf";  // AAVE V2 Lending Pool
const DAI = "0x8f3Cf7ad23Cd3CaDbD9735AFf958023239c6A063";  // DAI
const PUSH = "0xb3971BCef2D791bc4027BbfedFb47319A4AAaaAa";  // EPNSCommV1_5 (Proxy)
const ZKBOB_DEPOSIT = "0x668c5286ead26fac5fa944887f9d2f20f7ddf289";  // BOB: zkBob Direct Deposit
const ZKBOB = "0xB0B195aEFA3650A6908f15CdaC7D92F8a5791B0B";  // zkBOB
const PUSH_CREATOR = "0x48008aA5B9CA70EeFe7d1348bB2b7C3094426AA6";
const UMAV3 = "0x5953f2538f613e05baed8a5aefa8e6622467ad3d";

const ROUND_DURATION = 60;

describe("Pool Together (EIP-6551)", function () {
    let poolTogether6551: PoolTogether6551;
    let vrfCoordinator: VRFCoordinatorV2Mock;
    let poolAccount6551: PoolAccount6551;
    let mockERC721: MockERC721;

    let owner: Signer, addr1: Signer, addr2: Signer, addrs: Signer[];
    let ownerAccount: PoolAccount6551, addr1Account: PoolAccount6551, addr2Account: PoolAccount6551;

    /**
     * Creates a new EIP-6551 pool account.
     * @param tokenId token id.
     * @param signer signer.
     */
    async function create6551Account(tokenId: number, signer: Signer) : Promise<PoolAccount6551> {
        // Define the parameters for the createAccount function
        const implementation = poolAccount6551.address;
        const chainId = 137; // Polygon Mainnet Chain ID
        const tokenContract = mockERC721.address;
        const salt = ethers.utils.randomBytes(32);
        const initData = "0x"; // No initialization data

        // Call the createAccount function and wait for the transaction to be mined
        const tmp = PoolTogether6551__factory.connect(poolTogether6551.address, signer);
        const createAccountTx = await tmp.createAccount(implementation, chainId, tokenContract, tokenId, salt, initData);
        const receipt = await createAccountTx.wait();

        // Find the AccountCreated event in the receipt
        const event = receipt.events?.find((e) => e.event === "AccountCreated");
        const accountAddress = event?.args?.account;

        // Check the result
        expect(accountAddress).to.not.eq(ethers.constants.AddressZero);
        return PoolAccount6551__factory.connect(accountAddress, signer);
    }

    /**
     * Mint DAI balances.
     * @param accounts
     * @param amount
     */
    async function getDAIForAccounts(accounts: string[], amount: BigNumber) {
        // Get the DAI contract
        const DAIContract = await ethers.getContractAt("IERC20", DAI);

        // Impersonate the account
        await ethers.provider.send("hardhat_impersonateAccount", ["0x6ab291A9BB3C20F0017f2E93A6d1196842D09bF4"]);

        const impersonatedAccount = await ethers.provider.getSigner("0x6ab291A9BB3C20F0017f2E93A6d1196842D09bF4");

        // Mint Ether for the impersonated account
        let hexBalance = ethers.utils.hexStripZeros(ethers.utils.parseEther("100").toHexString());
        await ethers.provider.send(
            "hardhat_setBalance",
            ["0x6ab291A9BB3C20F0017f2E93A6d1196842D09bF4", hexBalance]
        );

        // For each account
        for (let i = 0; i < accounts.length; i++) {
            const account = accounts[i];

            // Transfer DAI from the impersonated account to the current account
            await DAIContract.connect(impersonatedAccount).transfer(account, amount);

            // Check the account's DAI balance
            const balance = await DAIContract.balanceOf(account);
            await expect(balance.gt(ethers.constants.Zero), "DAI mint failed.");
        }

        // Stop impersonating the account
        await ethers.provider.send("hardhat_stopImpersonatingAccount", ["0x6ab291A9BB3C20F0017f2E93A6d1196842D09bF4"]);
    }

    async function getUSDCForAccounts(accounts: string[], amount: BigNumber) {
        // Get the USDC contract
        const USDCContract = await ethers.getContractAt("IERC20", USDC);

        // Impersonate the account
        await ethers.provider.send("hardhat_impersonateAccount", ["0xe7804c37c13166ff0b37f5ae0bb07a3aebb6e245"]);

        const impersonatedAccount = await ethers.provider.getSigner("0xe7804c37c13166ff0b37f5ae0bb07a3aebb6e245");

        // Mint Ether for the impersonated account
        let hexBalance = ethers.utils.hexStripZeros(ethers.utils.parseEther("100").toHexString());
        await ethers.provider.send(
            "hardhat_setBalance",
            ["0xe7804c37c13166ff0b37f5ae0bb07a3aebb6e245", hexBalance]
        );

        // For each account
        for (let i = 0; i < accounts.length; i++) {
            const account = accounts[i];

            // Transfer USDC from the impersonated account to the current account
            await USDCContract.connect(impersonatedAccount).transfer(account, amount);

            // Check the account's USDC balance
            const balance = await USDCContract.balanceOf(account);
            await expect(balance.gt(ethers.constants.Zero), "USDC mint failed.");
        }

        // Stop impersonating the account
        await ethers.provider.send("hardhat_stopImpersonatingAccount", ["0xe7804c37c13166ff0b37f5ae0bb07a3aebb6e245"]);
    }

    /**
     * Approve DAI for accounts.
     * @param accounts
     * @param amount
     */
    async function approveDAIForAccounts(accounts: PoolAccount6551[], amount: BigNumber) {
        // Get the DAI contract
        const DAIContract = IERC20__factory.connect(DAI, owner);

        // For each account
        for (let i = 0; i < accounts.length; i++) {
            const account = accounts[i];

            // Prepare the calldata for the approve function
            const approveCalldata = DAIContract.interface.encodeFunctionData("approve", [poolTogether6551.address, amount]);

            // Call the executeCall function and wait for the transaction to be mined
            const executeCallTx = await account.executeCall(DAI, 0, approveCalldata);
            await executeCallTx.wait();

            // Check the allowance
            const allowance = await DAIContract.allowance(account.address, poolTogether6551.address);
            expect(allowance.gte(amount), "DAI approval failed.");
        }
    }

    /**
     * Deposit to pool with 6551 account.
     * @param amount
     * @param account
     */
    function depositToPool(amount: BigNumber, account: PoolAccount6551) {
        // Prepare the calldata for the depositDAI function
        const depositCalldata = poolTogether6551.interface.encodeFunctionData("depositDAI", [amount]);

        // Call the executeCall function and wait for the transaction to be mined
        return account.executeCall(poolTogether6551.address, 0, depositCalldata);
    }

    beforeEach(async function () {
        // Get factories.
        const PoolTogether6551Factory: PoolTogether6551__factory = await ethers.getContractFactory("PoolTogether6551");
        const VRFCoordinatorV2MockFactory: VRFCoordinatorV2Mock__factory = await ethers.getContractFactory("VRFCoordinatorV2Mock");
        const PoolAccount6551Factory: PoolAccount6551__factory = await ethers.getContractFactory("PoolAccount6551");
        const MockERC721Factory: MockERC721__factory = await ethers.getContractFactory("MockERC721");

        // Get signers.
        [owner, addr1, addr2, ...addrs] = await ethers.getSigners();

        // Deploy VRF.
        vrfCoordinator = await VRFCoordinatorV2MockFactory.deploy(0, 0);
        await vrfCoordinator.deployed();

        // Create subscription.
        await vrfCoordinator.createSubscription();
        await vrfCoordinator.fundSubscription(1, ethers.utils.parseEther("100"));

        // Deploy registry.
        poolTogether6551 = await PoolTogether6551Factory.deploy(
            1, // subscribe address,
            ROUND_DURATION, // 1 min,
            AAVE, // aave v2
            vrfCoordinator.address,
            DAI,
            USDC,
            PUSH,
            PUSH_CREATOR,
            UMAV3
        )
        await poolTogether6551.deployed();

        // Add VRF consumer.
        await vrfCoordinator.addConsumer(1, poolTogether6551.address);

        // Deploy PoolAccount6551.
        poolAccount6551 = await PoolAccount6551Factory.deploy();
        await poolAccount6551.deployed();

        // Deploy MockERC721.
        mockERC721 = await MockERC721Factory.deploy();
        await mockERC721.deployed();

        // Mint a token for the users
        await mockERC721.safeMint(await owner.getAddress());
        await mockERC721.safeMint(await addr1.getAddress());
        await mockERC721.safeMint(await addr2.getAddress());

        // Deploy 6551 accounts.
        ownerAccount = await create6551Account(0, owner);
        addr1Account = await create6551Account(1, addr1);
        addr2Account = await create6551Account(2, addr2);

        // Transfer DAI balance.
        // @dev Also adds DAI balance to the reserve for mocking prize.
        await getDAIForAccounts(
            [ownerAccount.address, addr1Account.address, addr2Account.address, poolTogether6551.address],
            ethers.utils.parseEther("50")
        );

        // Add USDC balance for UMA
        await getUSDCForAccounts(
            [poolTogether6551.address],
            ethers.utils.parseUnits("300", 9)
        );

        // Approve from accounts.
        await approveDAIForAccounts(
            [ownerAccount, addr1Account, addr2Account],
            ethers.constants.MaxUint256
        );
    });

    describe("EIP-6551 Account", () => {
        it("should have the right token and owner.", async () => {
            // Call the token function
            const ownerTokenDetails = await ownerAccount.token();
            const addr1TokenDetails = await addr1Account.token();
            const addr2TokenDetails = await addr2Account.token();

            // Check the result
            expect(ownerTokenDetails.chainId).to.equal(137);
            expect(ownerTokenDetails.tokenContract).to.equal(mockERC721.address);
            expect(ownerTokenDetails.tokenId).to.equal(ethers.BigNumber.from(0));

            expect(addr1TokenDetails.chainId).to.equal(137);
            expect(addr1TokenDetails.tokenContract).to.equal(mockERC721.address);
            expect(addr1TokenDetails.tokenId).to.equal(ethers.BigNumber.from(1));

            expect(addr2TokenDetails.chainId).to.equal(137);
            expect(addr2TokenDetails.tokenContract).to.equal(mockERC721.address);
            expect(addr2TokenDetails.tokenId).to.equal(ethers.BigNumber.from(2));

            // Call the owner function
            const ownerAddress = await ownerAccount.owner();
            const addr1Address = await addr1Account.owner();
            const addr2Address = await addr2Account.owner();

            // Check the result
            expect(ownerAddress).to.equal(await owner.getAddress());
            expect(addr1Address).to.equal(await addr1.getAddress());
            expect(addr2Address).to.equal(await addr2.getAddress());
        });
    });

    describe("Pool Together", () => {
        it("should allow accounts to deposit and then withdraw", async () => {
            // Define the deposit amount
            const depositAmount = ethers.utils.parseEther("1");

            // Get DAI contract instance
            const DAIContract = IERC20__factory.connect(DAI, owner);

            // Approve the PoolAccount contract to spend the deposit amount
            await DAIContract.approve(ownerAccount.address, depositAmount);

            // Prepare the calldata for the depositDAI function
            const depositCalldata = poolTogether6551.interface.encodeFunctionData("depositDAI", [depositAmount]);

            // Call the executeCall function and wait for the transaction to be mined
            const executeDepositCallTx = await ownerAccount.executeCall(poolTogether6551.address, 0, depositCalldata);
            await executeDepositCallTx.wait();

            // Check the result
            const ownerTicketAfterDeposit = await poolTogether6551.getUserTicket(ownerAccount.address);
            expect(ownerTicketAfterDeposit.deposit).to.equal(depositAmount);

            // Define the withdraw amount
            const withdrawAmount = ethers.utils.parseEther("1");

            // Prepare the calldata for the withdrawDAI function
            const withdrawCalldata = poolTogether6551.interface.encodeFunctionData("withdrawDAI", [withdrawAmount]);

            // Call the executeCall function and wait for the transaction to be mined
            const executeWithdrawCallTx = await ownerAccount.executeCall(poolTogether6551.address, 0, withdrawCalldata);
            await executeWithdrawCallTx.wait();

            // Check the result
            const ownerTicketAfterWithdraw = await poolTogether6551.getUserTicket(ownerAccount.address);
            expect(ownerTicketAfterWithdraw.deposit).to.equal(0);
        });

        it("should finish a round and select a winner", async () => {
            // Deposit the participants.
            const depositAmount = ethers.utils.parseEther("1");
            await depositToPool(depositAmount, ownerAccount);
            await depositToPool(depositAmount, addr1Account);
            await depositToPool(depositAmount, addr2Account);


            // Advance the block timestamp to make the round eligible for finishing.
            await ethers.provider.send("evm_increaseTime", [61 * 1000]); // extra seconds to surpass the 1-minute round duration.

            // Finish the round.
            // @dev the first total weight is reserved for registry.
            const roundId = poolTogether6551.getActiveRoundId();
            const weights = [0, 100, 50, 10]; // Assuming there's only one participant with 100 weight.
            const totalWeights = weights.reduce((partialSum, a) => partialSum + a, 0);
            await expect(
                poolTogether6551.connect(owner).finishRound(totalWeights, weights, true)
            ).to.emit(poolTogether6551, "RoundFinished")

            // Get the request id.
            const roundDetails = await poolTogether6551.finishedRounds(roundId);

            // Mock random number.
            const firstNumber = ethers.BigNumber.from(ethers.utils.randomBytes(32));

            // Call the callback.
            await expect(
                poolTogether6551.mockFulfillRandomWords(roundDetails.randomnessReqId, [firstNumber])
            ).to.emit(poolTogether6551, "WinnerSelected");
        });
    });

});
