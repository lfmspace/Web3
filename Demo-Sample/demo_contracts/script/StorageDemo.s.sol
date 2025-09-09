// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.13;

import {Script, console} from "forge-std/Script.sol";

import {StorageDemo} from "../src/Storage/StorageDemo.sol";

contract StorageDemoScript is Script {
    StorageDemo public v1;
    address owner;
    function setUp() public {}

    function run() public {
        vm.startBroadcast();
        v1 = new StorageDemo();
        vm.stopBroadcast();
    }
}
