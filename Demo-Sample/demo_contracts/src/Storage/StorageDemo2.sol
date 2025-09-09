// SPDX-License-Identifier: MIT
pragma solidity 0.8.25;

contract StorageDemo2 {
    bool private value_bool_single = true; //slot0
    uint256 private value_uint_256_a = 2; //slot1
    uint8 private value_uint_8_single = 3; //slot2
    uint256 private value_uint_256_c = 4; //slot3
    bytes12 private value_bytes_single; //slot4
    uint256 private value_uint_256_d; //slot5
    address private value_address_single; //slot6
    uint256 private value_uint_256_b = 6; //slot7
    bytes32 private value_bytes32_a; //slot8
    uint8 private value_uint_8_a; //slot9
    address private value_address_a; //slot9
    uint8 private value_uint_8; //slot9
    uint88 private value_uint_88; //slot10
    address private value_address_b; //slot10
    bytes12 private value_bytes12; //slot11
    address private value_address_c; //slot11
    bool private value_bool; //slot12
    uint8 private value_uint_16_a; //slot12
    address private value_address_d; //slot12
    uint16 private value_uint_16_b; //slot12
    uint80 private value_uint_80; //slot13
    address private value_address_e; //slot13
    bytes[2] private reference_bytes_array_fixed_length; //slot14  slot15
    bytes8[2] private reference_bytes8_array_fixed_length; //slot16  //slot16
    uint256[2] private reference_uint256_array_fixed_length; //slot17  //slot18
    uint8[2] private reference_uint8_array_fixed_length; //slot19 //slot19
    address[2] private reference_address_array_fixed_length; //slot20 //slot21
    bool[2] private reference_bool_array_fixed_length; //slot22 //slot22
    bytes private reference_bytes_a; //slot23
    bytes private reference_bytes_b; //slot24
    //length<31  //slot25(value + length*2)
    string private reference_string_length_less31;
    //length>31 //slot26(length*2+1)=>keccak256(16) 0&1
    string private reference_string_length_greater31;
    string[] private reference_string_array; //slot27
    bytes[] private reference_bytes_array; //slot28=
    bytes8[] private reference_bytes8_array; //slot29
    uint256[] private reference_uint256_array; //slot30
    uint8[] private reference_uint8_array; //slot31
    address[] private reference_address_array; //slot32
    bool[] private reference_bool_array; //slot33
    User userInfo; //slot34
    mapping(uint256 => User) private reference_struct_array; //slot35
    mapping(string => User) private reference_struct_array_string_key; //slot36
    struct User {
        address addr;
        uint8 age;
    }

    constructor() {
        reference_struct_array[1] = User(0xfc968Fbc5751Fb3863fc4764c0a66c76728e91eC, 18);
        reference_struct_array_string_key["user"] = User(0x714F6eA9909D934f02448EDd2D89deA8c3Bc83f9, 18);
    }

    function readStorageNb(uint256 slotNb) public view returns (bytes32 result) {
        assembly {
            result := sload(slotNb)
        }
    }

    function kecReadStorageNbKey(uint256 slot) public view returns (bytes32 result) {
        bytes32 ss = keccak256(abi.encodePacked(slot));
        assembly {
            result := sload(ss)
        }
    }

    function slotKeccak256(uint256 slot) public pure returns (bytes32 result) {
        result = keccak256(abi.encodePacked(slot));
    }
    function slotKeyKeccak256(uint256 slot, uint256 key) public pure returns (bytes32 result) {
        result = keccak256(abi.encodePacked(key, slot));
    }

    function stringKeyKeccak256(uint256 slot, string memory key) public pure returns (bytes32 result) {
        result = keccak256(abi.encodePacked(key, slot));
    }

    function readMappingValue(uint256 baseSlot, uint256 key) public view returns (bytes32 value, bytes32 slot) {
        //bytes32 slot;
        assembly {
            // 计算映射槽：keccak256(key . baseSlot)
            mstore(0x0, key)
            mstore(0x20, baseSlot)
            slot := keccak256(0x0, 0x40)
            value := sload(slot)
        }
    }
}
