//SPDX-License-Identifier: MIT
pragma solidity 0.8.25;

// 编写一个 Bank 合约，实现功能：

// 可以通过 Metamask 等钱包直接给 Bank 合约地址存款
// 在 Bank 合约记录每个地址的存款金额
// 编写 withdraw() 方法，仅管理员可以通过该方法提取资金。
// 用数组记录存款金额的前 3 名用户
//0x4838B106FCe9647Bdf1E7877BF73cE8B0BAD5f97
contract Bank {
    address owner;
    address[] public top;
    mapping(address=>uint256) public deposit;
    address[] depositPesons;
    uint8 constant topNum=3;
    error NotOwner();
    
    constructor(){
        owner=msg.sender;
    }

    function getBalance() public view returns(uint256){
        return address(this).balance;
    }

    function depositMoney() public payable virtual{
        address from=msg.sender;
        uint256 value=msg.value;
        //存钱
        deposit[from]+=value;
        topPush(from);
        bool  isExist=false;
       for (uint8 i=0; i<depositPesons.length; i++) 
        {
            if(depositPesons[i]==from){
                isExist=true;
                break;
            }
        }
        if(!isExist) depositPesons.push(from);
    } 

    //用户写入榜单
    function topPush(address depositPerson) internal {
        bool  isExist=false;
        //判断用户是否存在
        for (uint8 i=0; i<top.length; i++) 
        {
            if(top[i]==depositPerson){
                isExist=true;
                break;
            }
        }
        //不在榜单加进临时榜单，临时榜单数最大为topNum+1
        if(!isExist){
            if(top.length<topNum){
                top.push(depositPerson);
            }else if(deposit[depositPerson]>deposit[top[top.length-1]]){
                top[top.length-1]=depositPerson;
                top=topSort(top);
            }

        }

    }

    //榜单排序
    function topSort( address[] memory arr) internal view returns(address[] memory){
        for (uint8 i = 0; i < arr.length- 1; i++) {
            for (uint8 j = 0; j < arr.length- 1 - i; j++) {
                if (deposit[arr[j]] < deposit[arr[j+1]]) { // 相邻元素两两对比
                    address temp = arr[j+1];  // 元素交换
                    arr[j+1] = arr[j];
                    arr[j] = temp;
                }
            }
        }
        return arr;
    }

    event BankTake(address, uint256);
    function withdraw(uint256 amount) public {
        require(owner==msg.sender,"Not Owner");
        //if(!owner==msg.sender) revert NotOwner();

        //msg.sender.transfer(address(this).balance);
        (bool isSuccess,)=msg.sender.call{value:amount}("");

        require(isSuccess,"bank take");
        emit BankTake(msg.sender,amount);
    }

    event Received(address, uint256);
    receive() external payable {
        depositMoney();
        emit Received(msg.sender, msg.value);
     }
}