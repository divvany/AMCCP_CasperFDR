ecommerce.spl: agents directly communicate; no attacks

ecommerce2.spl: agents directly communicate; trivial secrecy attack

ecommerce3.spl: messages forwarded by merchant; no authentication between
customer and bank

ecommerce4.spl: signed messages forwarded by merchant; multiplicity attacks

ecommerce5.spl: signed messages with sequence numbers forwarded by merchant,
but not checked for uniqueness; same multiplicity attacks

ecommerce6.spl: signed messages with sequence numbers forwarded by merchant,
but not checked for uniqueness, and then returned; multiplicity attack one way

dha.spl: Diffie-Hellman over authenticated and secret channels, and exponents
sent 

dha2.spl: more sensible Diffie-Hellman, using authenticated channels
