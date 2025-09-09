//SPDX-License-Identifier: MIT
pragma solidity ^0.8.4;
import "./LToken.sol";

/*
• 编写⼀个TokenBank ，可以将 Token 存⼊ TokenBank:
• 记录每个⽤户存⼊的 token 数量
• 用户可以提取之前存入的Token （withdraw ⽅法）
0x4838B106FCe9647Bdf1E7877BF73cE8B0BAD5f97
*/
contract LTokenBank {
    address owner;
    mapping(address=>uint) public deposit;
    LToken public token;
    
    //error NotOwner();
    
    constructor(address addr){
        owner=msg.sender;
        token=LToken(addr);
    }

    function getBalance() public view returns(uint){
        return address(this).balance;
    }


    function depositMoney(uint256 amount) public returns(bool){
        //存钱
        bool success =token.transferFrom(msg.sender,address(this),amount);
        //由于有些代币transferForm可能没有返回值，实际项目需要考虑无返回值情况

        require(success,"get token fail");

        deposit[msg.sender]+=amount;
        return true;

    } 

    event Take(address, uint);
    function withdraw(uint amount) public returns (bool) {
        require(deposit[msg.sender]>=amount,"exceeds amount");
        bool isSuccess=token.transfer(msg.sender,amount);
        require(isSuccess," take fail");
        deposit[msg.sender]-=amount;
        emit Take(msg.sender,amount);
        return true;
    }


}