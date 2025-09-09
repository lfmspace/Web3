// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.13;

import {Script, console} from "forge-std/Script.sol";

import {RTNFT} from "../src/NFTRent/RTNFT.sol";

contract RTNFTScript is Script {
    RTNFT public v1;
    address owner;
    function setUp() public {}

    function run() public {
        // vm.startBroadcast();
        // owner = vm.parseAddress('0xD13107fB58a10E54fdFCA646Fe66C6Cc51B53AeC'); //管理员
        // console.log("manage is", owner);
        // v1 = new RTNFT(owner);
        // v1 = RTNFT(
        //     vm.parseAddress('0xD13107fB58a10E54fdFCA646Fe66C6Cc51B53AeC')
        // );
        // v1.mintNFT(
        //     owner,
        //     'https://blue-historical-centipede-170.mypinata.cloud/ipfs/bafybeihwnxxejptlvkm3bus7uvya5s6qrmijecygi3s23eh7zhp4vsebu4/%E5%85%94%E5%AD%90%E6%B3%A8%E8%A7%86.txt'
        // );
        // v1.mintNFT(
        //     owner,
        //     'https://blue-historical-centipede-170.mypinata.cloud/ipfs/bafybeihwnxxejptlvkm3bus7uvya5s6qrmijecygi3s23eh7zhp4vsebu4/%E5%8F%AF%E7%88%B1%E5%85%94%E5%AD%90.txt'
        // );
        // v1.mintNFT(
        //     owner,
        //     'https://blue-historical-centipede-170.mypinata.cloud/ipfs/bafybeihwnxxejptlvkm3bus7uvya5s6qrmijecygi3s23eh7zhp4vsebu4/%E5%A4%A7%E7%9C%BC.txt'
        // );
        // v1.mintNFT(
        //     owner,
        //     'https://blue-historical-centipede-170.mypinata.cloud/ipfs/bafybeihwnxxejptlvkm3bus7uvya5s6qrmijecygi3s23eh7zhp4vsebu4/%E6%89%93%E6%8B%9B%E5%91%BC.txt'
        // );
        // v1.mintNFT(
        //     owner,
        //     'https://blue-historical-centipede-170.mypinata.cloud/ipfs/bafybeihwnxxejptlvkm3bus7uvya5s6qrmijecygi3s23eh7zhp4vsebu4/%E7%B2%BE%E7%A5%9E%E5%85%94%E5%AD%90.txt'
        // );
        // v1.mintNFT(
        //     owner,
        //     'https://blue-historical-centipede-170.mypinata.cloud/ipfs/bafybeihwnxxejptlvkm3bus7uvya5s6qrmijecygi3s23eh7zhp4vsebu4/%E8%83%A1%E8%90%9D%E5%8D%9C.txt'
        // );
        vm.stopBroadcast();
    }
}
