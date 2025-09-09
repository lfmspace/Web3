// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.13;

import {Script, console} from 'forge-std/Script.sol';

import {LFMNFT} from '../src/NFTRent/LFMNFT.sol';

contract LFMNFTScript is Script {
    LFMNFT public v1;
    address owner;
    function setUp() public {
        owner = vm.envAddress('Manager'); //管理员
    }

    function run() public {
        vm.startBroadcast();
        //v1 = new LFMNFT(owner);
        v1 = LFMNFT(
            vm.parseAddress('0xaf834cdeEc821319Fa296ee74dfbcAe2deBD40D3')
        );
        // v1.mintNFT(
        //     owner,
        //     'https://blue-historical-centipede-170.mypinata.cloud/ipfs/bafybeihwnxxejptlvkm3bus7uvya5s6qrmijecygi3s23eh7zhp4vsebu4/%E5%85%94%E5%AD%90%E6%B3%A8%E8%A7%86.txt'
        // );
        // v1.mintNFT(
        //     owner,
        //     'https://blue-historical-centipede-170.mypinata.cloud/ipfs/bafybeihwnxxejptlvkm3bus7uvya5s6qrmijecygi3s23eh7zhp4vsebu4/%E5%8F%AF%E7%88%B1%E5%85%94%E5%AD%90.txt'
        // );
        v1.mintNFT(
            owner,
            'https://blue-historical-centipede-170.mypinata.cloud/ipfs/bafybeihwnxxejptlvkm3bus7uvya5s6qrmijecygi3s23eh7zhp4vsebu4/%E5%A4%A7%E7%9C%BC.txt'
        );
        v1.mintNFT(
            owner,
            'https://blue-historical-centipede-170.mypinata.cloud/ipfs/bafybeihwnxxejptlvkm3bus7uvya5s6qrmijecygi3s23eh7zhp4vsebu4/%E6%89%93%E6%8B%9B%E5%91%BC.txt'
        );
        v1.mintNFT(
            owner,
            'https://blue-historical-centipede-170.mypinata.cloud/ipfs/bafybeihwnxxejptlvkm3bus7uvya5s6qrmijecygi3s23eh7zhp4vsebu4/%E7%B2%BE%E7%A5%9E%E5%85%94%E5%AD%90.txt'
        );
        v1.mintNFT(
            owner,
            'https://blue-historical-centipede-170.mypinata.cloud/ipfs/bafybeihwnxxejptlvkm3bus7uvya5s6qrmijecygi3s23eh7zhp4vsebu4/%E8%83%A1%E8%90%9D%E5%8D%9C.txt'
        );
        vm.stopBroadcast();
    }
}
