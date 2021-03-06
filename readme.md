
<b>Automated Model Checking for Cryptographic Protocols with Casper&FDR</b>

************
About
************
If you use Casper and FDR directly, you must manually interpret the counterexample given by the model checking of the security protocol. This requires time and additional knowledge. Using this web platform you get a graphic representation of the counterexamples and also  information which helps you understand better the formal analysis concepts.

************
Installation
************
This app works on Linux OS only.


Application needs the following programs to be installed: 


-Apache  


-PHP (version 5.6 or newer)


-FDR3 (https://www.cs.ox.ac.uk/projects/fdr/manual/gui/getting_started.html)


-Haskell 


After downloading the files you have to run info_license.php file in your browser using server_address/info_license.php.

Before that you have to replace the last two lines from input_info_fdr file with some valid data in order to obtain a fdr license.
************
Demo
************
![Choose a protocol from Casper Library](images/choose_protocol.png)


![](images/protocol_representation.png)


![](images/press_check_protocol_from_library.png)


![](images/states.png)

The counterexample after pressing "Show"
![](images/counterexample.png)


![](images/fdr_top_level_trace.png)


![](images/fdr_system_level_trace.png)

