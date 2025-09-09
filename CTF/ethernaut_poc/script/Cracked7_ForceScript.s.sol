// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.0;

import {Script, console} from "forge-std/Script.sol";
import {Cracked1_Fallback} from "../src/Cracked1_Fallback.sol";

//forge script  --rpc-url sepolia --account metamask  Cracked7_ForceScript --broadcast
contract Cracked7_ForceScript is Script {
    Cracked1_Fallback public cracked;
    address ethernaut_contracts;

    function setUp() public {
        ethernaut_contracts = vm.parseAddress(vm.envString("Force_address"));
    }

    function run() public {
        vm.startBroadcast();
        cracked = new Cracked1_Fallback{value: 0.0000001 ether}(ethernaut_contracts);

        require(ethernaut_contracts.balance > 0, "cracked fail");
        vm.stopBroadcast();
    }
}
