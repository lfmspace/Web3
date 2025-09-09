// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.13;

import {Script, console} from 'forge-std/Script.sol';

import {MyNFTMarketV1} from '../src/NFT/MyNFTMarketV1.sol';
import '@openzeppelin/contracts/proxy/ERC1967/ERC1967Proxy.sol';
import '@openzeppelin/contracts/proxy/ERC1967/ERC1967Utils.sol';
import {MyNFT} from '../src/NFT/MyNFT.sol';
import {MyToken} from '../src/Token/MyToken.sol';

contract MyNFTMarketV1Script is Script {
    MyNFTMarketV1 public v1;
    ERC1967Proxy proxy;
    address owner;
    MyNFT nft;
    MyToken token;

    function setUp() public {
        owner = vm.envAddress('Manager'); //管理员
    }

    function run() public {
        //之前使用错误的初始化地址makeAddr('0xfc968Fbc5751Fb3863fc4764c0a66c76728e91eC'),导致owner出错
        // (address x, uint256 y) = makeAddrAndKey(
        //     '0xfc968Fbc5751Fb3863fc4764c0a66c76728e91eC'
        // );

        // vm.startBroadcast(y);
        // MyNFT(vm.parseAddress('0xa9251F12ecA95ba696Bf35a1965dfc38c22BF5Ec'))
        //     .transferOwnership(
        //         vm.parseAddress('0xfc968Fbc5751Fb3863fc4764c0a66c76728e91eC')
        //     );
        // MyNFTMarketV1(
        //     vm.parseAddress('0xE00F97DD8c1B9A34125F77d812c472492167140f')
        // ).transferOwnership(
        //         vm.parseAddress('0xfc968Fbc5751Fb3863fc4764c0a66c76728e91eC')
        //     );
        vm.startBroadcast();
        nft = new MyNFT(owner);

        token = new MyToken();
        v1 = new MyNFTMarketV1();

        proxy = new ERC1967Proxy(
            address(v1),
            abi.encodeCall(
                v1.initialize,
                (address(nft), address(token), address(owner))
            )
        );

        vm.stopBroadcast();
    }
}
