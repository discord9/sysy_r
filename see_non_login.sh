#!zsh
echo $SHELL
[[ $- == *i* ]] && echo 'Interactive' || echo 'not-interactive'
echo $LLVM_SYS_130_PREFIX
if [[ -o login ]]; then
  echo "I'm a login shell"
  else
  echo "I'm not a login shell"
fi

if [[ -o interactive ]]; then
  echo "I'm interactive"
  else
  echo "I'm not interactive"
fi
