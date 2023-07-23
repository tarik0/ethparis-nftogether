// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.0;

import "@openzeppelin/contracts/security/ReentrancyGuard.sol";

import "@openzeppelin/contracts/interfaces/IERC721.sol";
import "@openzeppelin/contracts/interfaces/IERC1271.sol";
import "@openzeppelin/contracts/token/ERC20/utils/SafeERC20.sol";
import "@openzeppelin/contracts/utils/Create2.sol";
import "@openzeppelin/contracts/utils/cryptography/SignatureChecker.sol";

import "../interfaces/IERC6551Account.sol";
import "../interfaces/IUniswapV2Router02.sol";
import "./libraries/Bytecode.sol";
import "../interfaces/IZkBobDirectDeposits.sol";

contract PoolAccount6551 is IERC6551Account {
    using SafeERC20 for IERC20;

    // TODO: do something with nonce ?
    uint256 internal _nonce = 0;

    ///
    /// Errors
    error OwnerOnly();

    ///
    /// Fallback to receive ether.
    receive() external payable {}

    ///
    /// Modifiers

    modifier onlyOwner() {
        if (msg.sender != owner())
            revert OwnerOnly();
        _;
    }

    ///
    /// External

    function swapAndDepositZkBOB(
        string memory zkAddress
    ) external onlyOwner {

        address bobAddress = 0xB0B195aEFA3650A6908f15CdaC7D92F8a5791B0B;
        address daiAddress = 0x8f3Cf7ad23Cd3CaDbD9735AFf958023239c6A063;
        address uniV2Router = 0xa5E0829CaCEd8fFDD4De3c43696c57F7D7A678ff;
        address bobQueue = 0x668c5286eAD26fAC5fa944887F9D2F20f7DDF289;

        IERC20 bob = IERC20(bobAddress);
        IERC20 dai = IERC20(daiAddress);
        IUniswapV2Router02 router = IUniswapV2Router02(uniV2Router);

        // Step 1: Swap DAI to BOB
        uint256 daiAmount = dai.balanceOf(address(this)); // Replace with the actual amount of DAI you want to swap
        address[] memory path = new address[](2);
        path[0] = daiAddress;
        path[1] = bobAddress;

        // Approve the Uniswap router to spend the DAI tokens
        dai.approve(daiAddress, daiAmount);

        // Perform the token swap
        router.swapExactTokensForTokens(
            daiAmount,
            0, // You can set a minimum amount of BOB tokens you want to receive to protect against price slippage
            path,
            address(this),
            block.timestamp
        );

        transferToZK(bob, bobQueue, zkAddress);
    }

    ///
    /// Internal

    function transferToZK(IERC20 bob, address bobQueue, string memory zkAddress) internal returns(uint256) {
        // Step 2: Send BOB tokens to ZkBobDirectDeposits
        uint256 bobAmount = bob.balanceOf(address(this));
        require(bobAmount > 0, "No BOB tokens to send");

        IZkBobDirectDeposits queue = IZkBobDirectDeposits(bobQueue);
        address fallbackReceiver = address(this);

        bob.approve(address(queue), bobAmount);
        uint256 depositId = queue.directDeposit(fallbackReceiver, bobAmount, zkAddress);
        return depositId;
    }

    ///
    /// ERC-6551 Account

    function executeCall(
        address to,
        uint256 value,
        bytes calldata data
    ) external payable returns (bytes memory result) {
        require(msg.sender == owner(), "Not token owner");

        bool success;
        (success, result) = to.call{value: value}(data);

        if (!success) {
            assembly {
                revert(add(result, 32), mload(result))
            }
        }
    }

    function token() external view returns (
        uint256 chainId,
        address tokenContract,
        uint256 tokenId
    ) {
        uint256 length = address(this).code.length;
        return abi.decode(
            Bytecode.codeAt(address(this), length - 0x60, length),
            (uint256, address, uint256)
        );
    }

    function owner() public view returns (address) {
        (uint256 chainId, address tokenContract, uint256 tokenId) = this.token();
        if (chainId != block.chainid) return address(0);

        return IERC721(tokenContract).ownerOf(tokenId);
    }

    function supportsInterface(bytes4 interfaceId) public pure returns (bool) {
        return (interfaceId == type(IERC165).interfaceId ||
            interfaceId == type(IERC6551Account).interfaceId);
    }

    function isValidSignature(bytes32 hash, bytes memory signature) external view returns (bytes4 magicValue) {
        bool isValid = SignatureChecker.isValidSignatureNow(
            owner(),
            hash,
            signature
        );

        if (isValid) {
            return IERC1271.isValidSignature.selector;
        }

        return "";
    }

    function nonce() external view override returns (uint256) {
        return _nonce;
    }
}