// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.25;

import "@solady/utils/FixedPointMathLib.sol";

//CURVE:y=a*(e^bx)
contract BondingCurve {
    using FixedPointMathLib for uint256;
    using FixedPointMathLib for int256;

    uint256 public immutable CURVE_PARAM_A;
    uint256 public immutable CURVE_PARAM_B;

    constructor(uint256 a, uint256 b) {
        CURVE_PARAM_A = a;
        CURVE_PARAM_B = b;
    }

    /// @dev 计算购买的代币数量 ln( detlaY*B/A + e^(B*X0) )/B-x0
    /// @param x0 当前代币供应量
    /// @param detlaY 购买价格
    /// @return 购买的代币数量
    function calculateBuy(uint256 x0, uint256 detlaY) external view returns (uint256) {
        int256 exp_0 = int256(detlaY.fullMulDiv(CURVE_PARAM_B, CURVE_PARAM_A));
        int256 exp_1 = exp_0 + int256(CURVE_PARAM_B.mulWad(x0)).expWad();

        uint256 detalX = uint256(exp_1.lnWad()).divWad(CURVE_PARAM_B) - x0;
        return detalX;
    }

    /// @dev 计算卖出金额 A*( (e^(B*x0)) - (e^( B*(x0-detlaX) )) )/B
    /// @param x0 当前代币供应量
    /// @param detlaX 卖出的代币数
    /// @return 卖出金额
    function calculateSell(uint256 x0, uint256 detlaX) external view returns (uint256) {
        require(x0 > detlaX, " token not enough");
        uint256 exp_0 = uint256(int256(CURVE_PARAM_B.mulWad(x0)).expWad());
        uint256 exp_1 = uint256(int256(CURVE_PARAM_B.mulWad(x0 - detlaX)).expWad());

        uint256 detalY = CURVE_PARAM_A.fullMulDiv((exp_1 - exp_0), CURVE_PARAM_B);
        return detalY;
    }
}
