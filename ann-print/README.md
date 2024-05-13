# Description 

This is an Ocaml library for a pretty-printing combinator library. It is based on François Pottier's Pprint library : https://github.com/fpottier/pprint.

It has the particularity of printing documents that can contain "annotated text" : we can box pieces of text in an "annotation" of any type. To print to plain text, we could simply ignore these annotations.

I developed this library in order to format text in Html. Inthis setting annotations correspond to a div and its attributes. 

# Author

Mathis Bouverot-Dupuis