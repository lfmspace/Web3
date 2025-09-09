// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.13;

import {Script, console} from "forge-std/Script.sol";
import {LToken} from "../src/LToken.sol";

contract LTokenScript is Script {
    LToken public token;

    function setUp() public {}

    function run() public {
        // string memory pk=vm.envString("SEPOLIA_KEYSTORE_ACCOUNT");
        // (address dp,)=deriveRememberKey(pk, 0);
        vm.startBroadcast();

        token = new LToken();

        vm.stopBroadcast();
    }
}
