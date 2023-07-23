# Sample Hardhat Project

This project demonstrates a basic Hardhat use case. It comes with a sample contract, a test for that contract, and a script that deploys that contract.

Try running some of the following tasks:

```shell
npx hardhat help
npx hardhat test
REPORT_GAS=true npx hardhat test
npx hardhat node
npx hardhat run scripts/deploy.ts
```

NFTogether allows users to leverage the power of Ethereum yield applications using their NFTs without any deposit loss.

The user requests the Registry contract named PoolTogether6551.sol to create an ERC6551 Account for the NFT they hold. The Registry Contract creates an ERC6551 Account linked to the NFT for the requesting users.

The user deposits a desired amount of DAI into the ERC6551 Account by calling the executeCall function located in the Registry Contract. The deposited DAI tokens are transferred to the AAVE DAI pool.

Every user of the application has a "weighted ticket" each round. This weight determines the user's chance of winning the draw. There are three parameters that determine the weight:

1) NFT Volume data obtained from Airstack: The NFT collection of the user's NFT is given as input and the volume of the NFT collection at that time is recorded.

2) The amount of APE tokens held in the ERC6551 account: The amount of APE Tokens held in the ERC6551 account of the NFT provides a bonus determined by thresholds to increase the user's weight.

3) The amount of DAI deposited into the AAVE pool via the ERC6551 wallet (Tickets): The amount of DAI deposited to participate in the pool provides the main basis on the weight.

All data required for weight is calculated off-chain and given to finishRound function as an uint array.

[Weights] = [Tickets] * ([APE Token Amount weight] + [NFT Volumes])

Weights at the uint array is provided such that their values at every index coincide with the corresponding user.
After the calculation of Weights, it is pushed to blockchain to select the winner.

Rewards on the protocol are distributed daily. At the end of the day, the income earned from the AAVE V3 DAI pool is transferred to the PoolRegistery6551.sol contract. The Weight information and Chainlink VRF service are used to determine the winning user.

The winning user is sent a notification that they have won using the Push Protocol. UMA OOV3 is also used to assert to the correctness of some off-chain process and store the output on-chain.

The amount won by the winning user is sent to the user's ERC6551 wallet. The money won can be withdrawn from the ERC6551 Account either as DAI or as BOB token via zkBOB direct deposits.

Link to our frontend: https://github.com/emremreistaken/NFTogetherApp