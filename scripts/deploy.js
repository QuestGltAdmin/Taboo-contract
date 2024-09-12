const hre = require("hardhat");

async function main() {

  const deployer= await ethers.getSigner();
  console.log("deployer address ", deployer.address);
  console.log("deployer balance ", (await deployer.getBalance())/1e18);
}

main().catch((error) => {
  console.error(error);
  process.exitCode = 1;
});
