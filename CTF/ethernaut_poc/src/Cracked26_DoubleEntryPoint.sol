// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

import "openzeppelin-contracts_4.0.0/access/Ownable.sol";
import "openzeppelin-contracts_4.0.0/token/ERC20/ERC20.sol";

interface IDetectionBot {
    function handleTransaction(address user, bytes calldata msgData) external;
}

interface IForta {
    function setDetectionBot(address detectionBotAddress) external;

    function notify(address user, bytes calldata msgData) external;

    function raiseAlert(address user) external;
}
interface IDoubleEntryPoint is IERC20 {
    function forta() external returns (address);
}

contract Cracked26_DetectionBot is IDetectionBot {
    address forta;
    address doubleEntryPoint;

    constructor(address _forta, address _doubleEntryPoint) {
        forta = _forta;
        doubleEntryPoint = _doubleEntryPoint;
    }

    function handleTransaction(address user, bytes calldata msgData) external {
        bytes calldata params = msgData[4:];
        address to;
        uint256 value;
        address origSender;

        (to, value, origSender) = abi.decode(params, (address, uint256, address));

        if (IDoubleEntryPoint(doubleEntryPoint).balanceOf(origSender) <= value) IForta(forta).raiseAlert(user);
    }
}
