## Software Foundations

Our answers to exercises in http://www.cis.upenn.edu/~bcpierce/sf

### Setting up your machine to do the exercises

1. Install Coq: http://coq.inria.fr/download
2. Configure vim for interactive proof

   ```viml
   " using Vundle for modules
   Bundle 'def-lkb/vimbufsync'
   Bundle 'the-lambda-church/coquille'
   
   " configure key bindings and colors
   augroup coqColors
     autocmd!
     autocmd BufReadPost *.v hi CheckedByCoq ctermbg=17 guibg=#111133
     autocmd BufReadPost *.v hi SentToCoq ctermbg=60 guibg=#222244
   augroup END

   map <silent> <leader>cs :CoqLaunch<cr>
   map <silent> <leader>cg :CoqToCursor<cr>
   map <silent> <leader>cn :CoqNext<cr>
   map <silent> <leader>cu :CoqUndo<cr>
   map <silent> <leader>cq :CoqKill<cr>
  
   map <silent> <leader>cx <C-w>l<C-w>L<C-w>t<C-w>K
   map <silent> <leader>cp :execute "Coq Print " . expand("<cword>") . "."<cr>
   ```
3. Download a copy of the book http://www.cis.upenn.edu/~bcpierce/sf/sf.tar.gz

### Edit and submit exercises.

1. Start with `Basics.v`, fill in the blanks, and ensure it passes
   the proof assistant: `coqc Basics.v`
2. Rename it to `[your_github_name]_Basics.v` and submit it
   as a pull request to this repo.

