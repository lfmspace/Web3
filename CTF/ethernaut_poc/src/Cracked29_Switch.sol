// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

contract Cracked29_Switch {
    bytes[] public array;

    function getMemory() public pure returns (bytes memory xx, bytes memory aa, bytes memory bb) {
        aa = abi.encodeWithSignature("turnSwitchOff()");
        bb = abi.encodeWithSignature("turnSwitchOn()");
        xx = abi.encodeWithSignature("flipSwitch(bytes)", aa, bb);
    }

    function getCall(bytes calldata aa) public pure returns (bytes memory xx) {
        xx = abi.encodeWithSignature("flipSwitch(bytes)", aa);
    }

    //偏移是从参数的起始位开始算，不算选择器
    function getStudyCall1() public returns (bytes[] memory rtnArry) {
        //bytes数组
        bytes[] memory bytsArr = new bytes[](2); //
        bytsArr[0] = hex"1234";
        bytsArr[1] = bytes("5678");
        array.push(abi.encode(bytsArr)); /*
        0x
0000000000000000000000000000000000000000000000000000000000000020
0000000000000000000000000000000000000000000000000000000000000002
0000000000000000000000000000000000000000000000000000000000000040
0000000000000000000000000000000000000000000000000000000000000080
0000000000000000000000000000000000000000000000000000000000000002
1234000000000000000000000000000000000000000000000000000000000000
0000000000000000000000000000000000000000000000000000000000000004
3536373800000000000000000000000000000000000000000000000000000000
        */

        rtnArry = array;
    }

    //偏移是从参数的起始位开始算，不算选择器
    function getStudyCall2() public returns (bytes[] memory rtnArry) {
        //bytes+string后面补0，整型+bool+地址前面补0，值类型无长度，动态数组+string+bytes有长度
        // 单个值类型
        uint256 a = 10;
        array.push(abi.encode(a)); // 0x000000000000000000000000000000000000000000000000000000000000000a

        address addr = 0xe74c813e3f545122e88A72FB1dF94052F93B808f;
        array.push(abi.encode(addr)); // 0x000000000000000000000000e74c813e3f545122e88a72fb1df94052f93b808f

        bool bol = true; //
        array.push(abi.encode(bol)); // 0x0000000000000000000000000000000000000000000000000000000000000001

        bytes5 bytValue = 0x1a2b3c4d5e; //
        array.push(abi.encode(bytValue)); // 0x1a2b3c4d5e000000000000000000000000000000000000000000000000000000

        //静态数组
        uint8[2] memory uintArr1 = [12, 78]; //定长数组无长度及偏移
        array.push(abi.encode(uintArr1)); //0x000000000000000000000000000000000000000000000000000000000000000c000000000000000000000000000000000000000000000000000000000000004e

        //单个引用类型
        bytes memory bytArr = hex"1234"; // 偏移32字节（0x20）-（偏移从参数编码开始位到长度起始位）  长度2
        array.push(abi.encode(bytArr)); // 0x000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000021234000000000000000000000000000000000000000000000000000000000000

        string memory str = "abcd"; // 占一个字节
        array.push(abi.encode(str)); // 0x000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000046162636400000000000000000000000000000000000000000000000000000000

        //动态数组
        uint96[] memory uintArr2 = new uint96[](2);
        uintArr2[0] = 1;
        uintArr2[1] = 2;
        array.push(abi.encode(uintArr2)); //0x0000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000002

        //多类型                            //动态类型在其顺序位放偏移量，数据放到最后（偏移量从参数编码开始（不含函数选择器）到字段的长度）
        array.push(abi.encode(a, uintArr2)); //0x000000000000000000000000000000000000000000000000000000000000000a0000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000002
        rtnArry = array;
    }
}

contract Switch {
    bool public switchOn; // switch is off
    bytes4 public offSelector = bytes4(keccak256("turnSwitchOff()"));

    modifier onlyThis() {
        require(msg.sender == address(this), "Only the contract can call this");
        _;
    }

    modifier onlyOff() {
        // we use a complex data type to put in memory
        bytes32[1] memory selector;
        // check that the calldata at position 68 (location of _data)
        assembly {
            calldatacopy(selector, 68, 4) // grab function selector from calldata
        }
        require(selector[0] == offSelector, "Can only call the turnOffSwitch function");
        _;
    }

    function flipSwitch(bytes memory _data) public onlyOff {
        (bool success, ) = address(this).call(_data);
        require(success, "call failed :(");
    }

    function turnSwitchOn() public onlyThis {
        switchOn = true;
    }

    function turnSwitchOff() public onlyThis {
        switchOn = false;
    }
}
