

import ConnectButton from "@/components/ConnectButton";

export default function Navbar() {
  const isConnected = false;
  const isdark = true;
  const toggleDarkMode = () => {};

  return (
    <header>
        <div className="px-5">
            <ConnectButton></ConnectButton>
          </div>
    </header>
  );
}
