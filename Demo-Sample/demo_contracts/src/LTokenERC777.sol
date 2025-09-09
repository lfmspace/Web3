//SPDX-License-Identifier: MIT
pragma solidity ^0.8.4;
//import "@openzeppelin/contracts/token/ERC777/ERC777.sol";


/*
发⾏⼀个具备回调功能的 ERC20 Token
• 扩展 TokenBank， 实现在转账回调中，将 Token 存⼊
TokenBank
不在此实现
*/

contract LTokenERC777 /**is ERC777**/{
  
//  function send(address _from,address _to,uint256 _value) public returns(bool success){
//     require(balances[_from]>=_value,"ERC20:transfer amount exceeds balance");
//     require(allowances[_from][msg.sender]>=_value,"ERC20:transfer amount exceeds allowances");
//     balances[_from]-=_value;
//     allowances[_from][msg.sender]-=_value;
//     balances[_to]+=_value;
//     emit Transfer(_from,_to,_value);
//     return true;
//  }  
  
 }    
  
