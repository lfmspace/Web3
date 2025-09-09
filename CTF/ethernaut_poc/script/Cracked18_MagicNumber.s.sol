// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.20;

import {Script, console} from "forge-std/Script.sol";

interface IMagicNum {
    function setSolver(address _solver) external;
}

//forge script  --rpc-url sepolia --account metamask  Cracked18_MagicNumberScript --broadcast
contract Cracked18_MagicNumberScript is Script {
    address ethernaut_contracts;

    function setUp() public {
        ethernaut_contracts = vm.parseAddress(vm.envString("MagicNumber_address"));
    }

    function run() public {
        vm.startBroadcast();
        address attack;
        assembly {
            let ptr := mload(0x40)
            mstore(ptr, shl(0x68, 0x69602A60005260206000F3600052600A6016F3))
            attack := create(0, ptr, 0x13)
        }
        console.log("ins is", attack);
        IMagicNum(ethernaut_contracts).setSolver(attack);

        vm.stopBroadcast();
    }
}
