//SPDX-License-Identifier: MIT
pragma solidity ^0.8.4;
import "./Bank.sol";

/*
bank2
编写⼀个 BigBank 合约继承⾃Bank，要求：
• 仅 >0.001 ether（⽤modifier权限控制）可以存款
• 把管理员转移给 Ownable 合约，只有 Ownable 可以调⽤ BigBank 的
withdraw()
*/

contract BigBank is Bank{
    modifier MoneyLimit{
        require(msg.value>0.001*10**18,"little money");
        _;
    }

    modifier IsOwner(){
        require(msg.sender==owner,"not owner");
        _;
    }

    function changeOwner(address newOwner) public IsOwner(){
        owner=newOwner;
    }

    function depositMoney() public payable override MoneyLimit{
        super.depositMoney();
    }

}