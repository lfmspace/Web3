//nft信息
export interface NFTInfo {
  id: string;
  tokenId: bigint;
  ca: string;
  tokenURL: string;
  blockTimestamp: string;
  name: string;
  owner: string;
}

/*
 * @description: NFT出租信息
 */
export interface RentoutOrderMsg {
  maker: string; // 租户地址
  nft_ca: string; // NFT合约地址
  token_id: bigint; // NFT tokenId
  daily_rent: bigint; // 每日租金
  max_rental_duration: bigint; // 最大租赁时长
  min_collateral: bigint; // 最小抵押
  list_endtime: bigint; // 挂单结束时间
}

export interface RentoutOrderEntry extends RentoutOrderMsg {
  id: number;
  token_url: string;
  token_name: string;
  signature: string;
  created_at: string;
}

// 类型守卫函数
export function isRentoutOrderMsg(data: unknown): data is RentoutOrderMsg {
  return (
    typeof data === "object" &&
    data !== null &&
    "maker" in data &&
    "nft_ca" in data &&
    "token_id" in data &&
    "daily_rent" in data &&
    "max_rental_duration" in data &&
    "min_collateral" in data &&
    "list_endtime" in data
  );
}
