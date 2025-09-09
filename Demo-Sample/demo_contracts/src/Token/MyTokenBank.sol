// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.25;

import "./MyToken.sol";

//只存MyToken的银行
contract MyTokenBank {
    MyToken public _token;
    // 1. 保存token的持有者
    mapping(address => uint) public _balances;

    event BalanceChange(address from, address to, uint256 amount);
    error DepositFail(address user, uint256 amount,string msg);

    constructor(address token){
        _token = MyToken(token);
    }

    /**
    存款流程：
    1.用户调用Token中的授权方法
    2.再调用该方法存款 
    */
    function desposit(uint256 amount) public  returns(bool){
        try _token.transferFrom(msg.sender, address(this), amount){
            _balances[msg.sender] += amount;
            emit BalanceChange(msg.sender, address(this), amount);
            return true;
        }catch Error(string memory reason){
            revert DepositFail(msg.sender, amount,reason);
        }catch (bytes memory reason){
            revert DepositFail(msg.sender, amount,string(reason));
        }
    }

    /**
    存款流程：
    1.用户调用Token中的send方法
    2.合约中的send方法会调用该方法存款 
    */
    function TransferReceipt(address from,  uint256 amount) public returns(bool){
        _balances[from]+=amount;
        emit BalanceChange(from, address(this), amount);
        return true;
    }
    
    
    /**
    存款流程：
    1.用户签名授权提交
    2.本合约代理调用并记录存款明细 
    */
    function permitDeposit(uint256 amount,uint256 deadline,uint8 v,bytes32 r,bytes32 s) public returns(bool){
        _token.permit(msg.sender,address(this),amount,deadline,v,r,s);
        _token.transferFrom(msg.sender, address(this), amount);
        _balances[msg.sender]+=amount;
        emit BalanceChange(msg.sender, address(this), amount);
         return true;
    }

}
