// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.13;

import {Script, console} from 'forge-std/Script.sol';
import {MyNFTMarketV2} from '../src/NFT/MyNFTMarketV2.sol';

import {MyNFTMarketV1} from '../src/NFT/MyNFTMarketV1.sol';

contract MyNFTMarketV2Script is Script {
    MyNFTMarketV2 public v2;

    function setUp() public {}

    function run() public {
        //address owner = vm.evn('Manager'); //管理员
        vm.startBroadcast();
        // consol.log('msgsender is', msg.sender);
        // consol.log(
        //     'MyNFTMarketV1 owner is',
        //     MyNFTMarketV1(
        //         vm.parseAddress('0xE00F97DD8c1B9A34125F77d812c472492167140f')
        //     ).ower()
        // );
        v2 = new MyNFTMarketV2(
            vm.parseAddress('0xa9251F12ecA95ba696Bf35a1965dfc38c22BF5Ec'),
            vm.parseAddress('0xaEED8200bD55427C6f003311810dBc895C431E71')
        );
        console.log('new success');
        MyNFTMarketV1(
            vm.parseAddress('0xE00F97DD8c1B9A34125F77d812c472492167140f')
        ).upgradeToAndCall(
                address(v2),
                abi.encodeCall(v2.initialize, ('MyNFTMarket', '1'))
            );

        vm.stopBroadcast();
    }
}
