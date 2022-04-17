Exp -> AddExp
means 
1==2;
is not a legal stmt

rm ~/.cargo/.package-cache
to stop `cargo meatdata` to run incorrectly

https://reimbar.org/dev/rust-vscode-terminal/
Running Rust tests from VS Code terminal
Even if your .zshrc or .zprofile are correctly configured with the path to the Rust environment, VSCode is popping a new task without using your login session, so it is not aware of your configuration!

To fix this, you need to provide the path in your .zshenv file as well. If you don’t have a .zshenv yet, you can just copy your existing configuration:

set .zshenv or /etc/zshenv doesn't seem to be working
set /etc/environment doesn't work neither, something is wrong

auto test from rust-analyzer can't regonize LLVM_SYS_130_PREFIX of system-wide LLVM
could be a bug with zsh for non-login non-interactive shell
not worth it, seems no global setting for `cargo test` env var on compile time.