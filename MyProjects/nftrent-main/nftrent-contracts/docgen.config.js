module.exports = {
  input: './src',    // 源码目录
  output: './docs',        // 输出目录
  templates: './templates', // 可自定义模板目录（可选）
  clearOutput: true,       // 生成前清空输出目录
  runOnCompile: true       // 编译时自动生成文档（配合 Hardhat/Truffle）
};
