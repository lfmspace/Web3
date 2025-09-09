pragma solidity 0.8.25;

import '@openzeppelin/contracts/proxy/Clones.sol';
import {Ownable} from '@openzeppelin/contracts/access/Ownable.sol';
import './Meme.sol';
import {Test, console} from 'forge-std/Test.sol';

contract MemeFactory is Ownable {
    address _logic;
    constructor(address logic, address owner) Ownable(owner) {
        _logic = logic;
    }

    function deployMeme(
        string memory symbol,
        uint256 totalSupply,
        uint256 perMint,
        uint256 price
    ) public returns (address) {
        address proxy = Clones.clone(_logic);
        Meme(proxy).init(
            symbol,
            totalSupply,
            perMint,
            price,
            owner(),
            msg.sender
        );
        return proxy;
    }
}
