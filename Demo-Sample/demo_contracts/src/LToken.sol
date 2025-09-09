//SPDX-License-Identifier: MIT
pragma solidity ^0.8.4;

/*
⾃⼰写⼀个Token，并部署（ERC20） 
• 编写⼀个TokenBank ，可以将 Token 存⼊ TokenBank:
• 记录每个⽤户存⼊的 token 数量
• 管理员可以提取所有的Token （withdraw ⽅法）
*/

contract LToken{
 string public name ;
 string public symbol ;
 uint8 public decimals ;
 uint256 public totalSupply ;

 constructor(){
    name="LeiToken";
    symbol="LT";
    decimals=18;
    totalSupply=100000000*10**decimals;
    balances[msg.sender]=totalSupply;
 }

 mapping(address=>uint256) public balances ;
 mapping(address=>mapping(address=>uint256)) public allowances ;

 event Transfer(address indexed _from, address indexed _to,uint256 _value);
 event Approve(address indexed _from, address indexed _spender,uint256 _value);
 function balanceOf(address _owner) public view returns(uint256 balance){
    return balances[_owner];
 }
 function transfer(address _to,uint256 _value) public returns(bool success){
    require(balances[msg.sender]>=_value,"ERC20:transfer amount exceeds balance");
    balances[msg.sender]-=_value;
    balances[_to]+=_value;
    emit Transfer(msg.sender,_to,_value);
    return true;
 }    
 function transferFrom(address _from,address _to,uint256 _value) public returns(bool success){
    require(balances[_from]>=_value,"ERC20:transfer amount exceeds balance");
    require(allowances[_from][msg.sender]>=_value,"ERC20:transfer amount exceeds allowances");
    balances[_from]-=_value;
    allowances[_from][msg.sender]-=_value;
    balances[_to]+=_value;
    emit Transfer(_from,_to,_value);
    return true;
 }  
  function approve(address _spend,uint256 _value) public returns(bool success){
    allowances[msg.sender][_spend]=_value;
    emit Approve(msg.sender,_spend,_value);
    return true;
 }  
 function allowance(address _owner,address _spend) public view returns(uint256 ){
    return allowances[_owner][_spend];
 }  

 function applyTestToken(address _addr,uint amount) public returns(bool ){
   require(1!=1,"saasasa");
   balances[_addr]+=amount;
   return true;
 }    
  
}