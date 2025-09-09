// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.13;

import {Script, console} from "forge-std/Script.sol";

import "../src/NFTRent/RTRentMarket.sol";
import {RTNFT} from "../src/NFTRent/RTNFT.sol";

//forge script  --rpc-url sepolia --account metamask  script/RTRentMarket.s.sol --broadcast --verify
contract RTRentMarketScript is Script {
    RTRentMarket public market;
    RTNFT public nft;
    address owner;
    function setUp() public {}

    function run() public {
        vm.startBroadcast();
        owner = vm.parseAddress("0xfc968Fbc5751Fb3863fc4764c0a66c76728e91eC");
        console.log("manage is", owner);
        nft = new RTNFT(owner);
        market = new RTRentMarket(address(nft), owner);

        nft.mintNFT(owner, "https://blue-historical-centipede-170.mypinata.cloud/ipfs/bafybeihwnxxejptlvkm3bus7uvya5s6qrmijecygi3s23eh7zhp4vsebu4/%E5%85%94%E5%AD%90%E6%B3%A8%E8%A7%86.txt");
        nft.mintNFT(owner, "https://blue-historical-centipede-170.mypinata.cloud/ipfs/bafybeihwnxxejptlvkm3bus7uvya5s6qrmijecygi3s23eh7zhp4vsebu4/%E5%8F%AF%E7%88%B1%E5%85%94%E5%AD%90.txt");
        nft.mintNFT(owner, "https://blue-historical-centipede-170.mypinata.cloud/ipfs/bafybeihwnxxejptlvkm3bus7uvya5s6qrmijecygi3s23eh7zhp4vsebu4/%E5%A4%A7%E7%9C%BC.txt");
        nft.mintNFT(owner, "https://blue-historical-centipede-170.mypinata.cloud/ipfs/bafybeihwnxxejptlvkm3bus7uvya5s6qrmijecygi3s23eh7zhp4vsebu4/%E6%89%93%E6%8B%9B%E5%91%BC.txt");
        nft.mintNFT(owner, "https://blue-historical-centipede-170.mypinata.cloud/ipfs/bafybeihwnxxejptlvkm3bus7uvya5s6qrmijecygi3s23eh7zhp4vsebu4/%E7%B2%BE%E7%A5%9E%E5%85%94%E5%AD%90.txt");
        nft.mintNFT(owner, "https://blue-historical-centipede-170.mypinata.cloud/ipfs/bafybeihwnxxejptlvkm3bus7uvya5s6qrmijecygi3s23eh7zhp4vsebu4/%E8%83%A1%E8%90%9D%E5%8D%9C.txt");

        vm.stopBroadcast();
    }
}
