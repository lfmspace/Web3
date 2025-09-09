// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.25;

import "@openzeppelin/contracts/token/ERC20/extensions/ERC20Permit.sol";
import "@openzeppelin/contracts/token/ERC20/ERC20.sol";

contract MyToken is ERC20,ERC20Permit {
        constructor() ERC20("MyToken","MTK") ERC20Permit("MyToken"){
        super._mint(msg.sender,10000000*10**18);
    }
    function applyToken(address to) public{
         super._mint(to,100*10**18);
    }

    event HookError(address from, address to, uint amount,string  reason);
    function send (address to, uint amount) public {
        super._transfer(msg.sender, to, amount);
        bytes memory data=abi.encodeWithSignature("TransferReceipt(address,uint256)", msg.sender,amount );
        (bool success,) = to.call(data);
        if (!success) {
            emit HookError(msg.sender,to,amount,"call transfer hook return false");
        }
    }
    
}

