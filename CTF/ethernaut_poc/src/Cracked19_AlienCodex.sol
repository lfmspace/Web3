// SPDX-License-Identifier: MIT
pragma solidity ^0.5.0;

contract AlienCodex {
    address public _owner;
    bool public contact;
    bytes32[] public codex;

    modifier contacted() {
        assert(contact);
        _;
    }

    function makeContact() public {
        contact = true;
    }

    function record(bytes32 _content) public contacted {
        codex.push(_content);
    }

    function retract() public contacted {
        codex.length--;
    }

    function revise() public {
        uint256 key = 1;
        uint256 dd = uint256(keccak256(abi.encodePacked(key)));
        uint256 max = (1 << 256) - 1;
        uint256 xx = max - dd + 1;
        codex[xx] = 0xad7c5bef027816a800da1736444fb58a807ef4c9603b7848673f7e3a68eb14a5;
    }

    function sub() public pure returns (uint256 s) {
        uint256 key = 1;
        uint256 dd = uint256(keccak256(abi.encodePacked(key)));
        uint256 max = (1 << 256) - 1;
        uint256 xx = max - dd + 1;
        s = xx;
    }

    function sub2() public pure returns (bytes32) {
        bytes32 ss = bytes32(uint256(0xfc968Fbc5751Fb3863fc4764c0a66c76728e91eC));
        return ss;
    }
}
