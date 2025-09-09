// SPDX-License-Identifier: MIT
pragma solidity 0.8.25;
library StringUtils {
    bytes16 private constant _HEX_SYMBOLS = '0123456789abcdef';
    function toHexString(bytes32 data) public pure returns (string memory) {
        bytes memory str = new bytes(64); // bytes32是32字节，每字节2个16进制字符
        for (uint256 i = 0; i < 32; i++) {
            uint8 byteValue = uint8(data[i]);
            str[2 * i] = _HEX_SYMBOLS[byteValue >> 4]; // 高4位
            str[2 * i + 1] = _HEX_SYMBOLS[byteValue & 0x0f]; // 低4位
        }
        return string(str);
    }

    function safeBytesToString(
        bytes memory _bytes
    ) public pure returns (string memory) {
        bytes memory strBytes = new bytes(_bytes.length);

        for (uint256 i; i < _bytes.length; ) {
            // 确保字节在可打印ASCII范围内 (32-126)
            strBytes[i] = (uint8(_bytes[i]) >= 32 && uint8(_bytes[i]) <= 126)
                ? _bytes[i]
                : bytes1(' ');

            unchecked {
                ++i;
            }
        }

        return string(strBytes);
    }
}
