<?php
/**
 * Created by PhpStorm.
 * User: andreea
 * Date: 16.05.2018
 * Time: 11:30
 */

class CheckProtocol extends CI_Controller
{


    function __construct()
    {
        parent::__construct();
        $this->load->library('form_validation');
        $this->load->library('session');
        $this->load->helper('url');


    }


    public function index()
    {

        $this->load->view('includes/header');


        $this->load->helper('file');

        $file = fopen("fdr_result", "r");
        $fileContent = fread($file, filesize("fdr_result"));
        fclose($file);


        if (!empty($fileContent)) {


            $assertionStrings = explode('Checking:', trim($fileContent));

            $info = explode('Loading', trim($assertionStrings[0]));

            $data['fdr_version'] = $info[0];

            if (count($info) > 1) {

                if (strpos($info[1], 'file') === false) {

                    $info[1] = str_replace("./documents", "CasperLibrary", $info[1]);

                } else {

                    $info[1] = str_replace("./documents/", "", $info[1]);

                }

                $data['filename'] = $info[1];
            } else {

                $data['filename'] = "";
            }




            $nrStrings = 0;
            $nrCounterexamples = 0;
            $atackNumber = 0;
            $strings = array();
            $propertyStrings = array();
            $fdrTraceLevel1 = array();
            $casperTraceLevel1 = array();
            $fdrFullTrace = array();
            $casperFullTrace = array();
            $assertionInfo = array();


            for ($i = 1; $i < count($assertionStrings); $i++) {


                $strings_explode = explode('Result:', trim($assertionStrings[$i]));
                $counterexampleStrings[$nrStrings] = -1;


                if (isset($strings_explode[1])) {


                    $result_explode = explode('Counterexample_type:', $strings_explode[1]);


                    $cTerType = "";
                    $behaviour = "";


                    if (count($result_explode) > 1) {


                        $counterexample = explode('behaviour_type:', $result_explode[1]);

                        $cTerType = $counterexample[0];

                        $stringEvent = explode('trace with event ', $cTerType);

                        $errorEvent = $stringEvent[1];

                        if (strpos($cTerType, 'trace with event') !== false) {

                            for ($j = 1; $j < count($counterexample) - 1; $j++) {


                                $behType = explode('Trace:', $counterexample[$j]);


                                if (strpos($behType[0], 'irrelevant') === false) {


                                    $behaviour = $behType[0];

                                    $trace = explode("End", $behType[1]);


                                    $traceLevel1Flag = false;


                                    if (trim($trace[0]) !== "") {

                                        $traceLevel1 = $trace[0];

                                        $fdrTraceLevel1[$atackNumber] = $this->writeTrace1ForInterpretFile($traceLevel1, $errorEvent);

                                        shell_exec('./call_interpret1');

                                        $casperTraceLevel1[$atackNumber] = $this->readFileResultInterpretTrace1();

                                        $atackNumber++;

                                        $traceLevel1Flag = true;

                                    }

                                    if ($traceLevel1Flag === true) {

                                        break;

                                    }

                                }


                            }


                            $behType = explode('Trace:', $counterexample[count($counterexample) - 1]);

                            $trace = explode("End", $behType[1]);

                            $traceLevel1 = $trace[0];

                            $fdrFullTrace[$atackNumber - 1] = $this->writeFullTraceForInterpretFile($traceLevel1, $errorEvent);

                            shell_exec('./call_interpret2');

                            $casperFullTrace[$atackNumber - 1] = $this->readFileResultInterpretFullTrace();

                            $counterexampleStrings[$nrStrings] = $nrCounterexamples;
                            $nrCounterexamples++;

                        }


                    }
                }

                $strings[$nrStrings] = array(
                    'ass_string' => $strings_explode[0],
                    'result' => $result_explode[0],
                    'counterexample_type' => $cTerType,
                    'behaviour_type' => $behaviour,
                );


                $propertyStrings[$nrStrings] = $strings_explode[0];


                $nrStrings++;

            }

        }


        $data["strings"] = $strings;

        $data["fdrTraceLevel1"] = $fdrTraceLevel1;

        $data["casperTraceLevel1"] = $casperTraceLevel1;

        $data["fdrFullTrace"] = $fdrFullTrace;

        $data["casperFullTrace"] = $casperFullTrace;

        $data["results"] = $assertionInfo;

        if (isset($_SESSION['description'])) {

            $data["description"] = $_SESSION['description'];
        } else {
            $data["description"] = "";
        }


        if (isset($_SESSION['agents'])) {

            $data["agents"] = $_SESSION['agents'];
        } else {
            $data["agents"] = "";
        }


        if (isset($_SESSION['free_vars'])) {

            $data["free_vars"] = $_SESSION['free_vars'];
        } else {
            $data["free_vars"] = "";
        }


        if (isset($_SESSION['specification'])) {

            $specification = $_SESSION['specification'];
        } else {
            $specification = "";
        }


        $finalPropStrings = array();

        if (count($propertyStrings) > 0) {


            foreach ($propertyStrings as $j => $propertyString) {
                $finalPropStrings[$j]["checked"] = false;
                $finalPropStrings[$j]["string"] = "";
                $finalPropStrings[$j]["nr"] = $counterexampleStrings[$j];

            }


            if ($specification !== "") {

                $tokens = explode("*", $specification);

                $nrSecret = 0;

                foreach ($tokens as $k => $token) {

                    $aux = explode("(", $token);

                    $property = trim($aux[0]);

                    $secret = false;

                    foreach ($propertyStrings as $j => $propertyString) {


                        if (stripos($propertyString, $property) !== false) {

                            if (!$finalPropStrings[$j]["checked"]) {

                                if (strcmp($property, "Agreement") === 0) {

                                    $actors = explode(",", $aux[1]);

                                    if ((stripos($actors[0], "b") !== false) && (strpos($propertyString, "RESPONDERToINITIATORAgreement") !== false)) {

                                        $finalPropStrings[$j]["string"] = $token;
                                        $finalPropStrings[$j]["checked"] = true;

                                    }

                                    if ((stripos($actors[0], "a") !== false) && (strpos($propertyString, "INITIATORToRESPONDERAgreement") !== false)) {

                                        $finalPropStrings[$j]["string"] = $token;
                                        $finalPropStrings[$j]["checked"] = true;

                                    }


                                } else {


                                    if (strcmp($property, "Secret") === 0) {

                                        if (!$secret) {

                                            $finalPropStrings[$j]["string"] = $token;
                                            $finalPropStrings[$j]["checked"] = true;
                                            $secret = true;
                                            $nrSecret++;
                                        }

                                    } else {

                                        $finalPropStrings[$j]["string"] = $token;
                                        $finalPropStrings[$j]["checked"] = true;

                                    }


                                }


                            }

                        }

                    }

                    if ($nrSecret !== 2) {
                        $finalPropStrings[1]["string"] = $finalPropStrings[0]["string"];

                    }

                }


            }


            $data["prop_strings"] = $finalPropStrings;

        }

        $this->load->view('checkProtocol/index', $data);
        $this->load->view('includes/footer');


    }


    function writeFullTraceForInterpretFile($trace, $error_event)
    {


        $trace = str_replace(' ', '', $trace);

        $trace_string = explode("*", $trace);


        $trace_for_interpret = "interpret\n";

        $show_trace = array();

        foreach ($trace_string as $k => $item) {

            $trace_for_interpret = $trace_for_interpret . $item . "\n";
            $show_trace[$k] = $item;

        }

        $trace_for_interpret = trim($trace_for_interpret) . PHP_EOL;

        file_put_contents('./inputs/input_full_trace', $trace_for_interpret . "\n");

        return $show_trace;


    }


    function writeTrace1ForInterpretFile($trace, $error_event)
    {

        $trace_string = explode("*", $trace);

        $trace_for_interpret = "interpret\n";

        $show_trace = "";

        foreach ($trace_string as $item) {

            if (strpos(trim($item), ' ') === false) {

                $trace_for_interpret = $trace_for_interpret . $item . "\n";
                $show_trace = $show_trace . $item . "<br>";
            }

        }

        $trace_for_interpret = trim($trace_for_interpret) . "\n" . trim($error_event) . PHP_EOL;

        $show_trace = substr($show_trace, 0, -4);

        $show_trace = trim($show_trace) . trim($error_event);

        file_put_contents('./inputs/input_trace1', $trace_for_interpret . "\n");

        return $show_trace;

    }

    function getProtocolDescription()
    {

        $_SESSION['description'] = $_POST['description'];
    }


    function getActualVariables()
    {

        $_SESSION['agents'] = $_POST['agents'];
    }

    function getFreeVariables()
    {

        $_SESSION['free_vars'] = $_POST['free_vars'];

    }

    function getProtocolSpecification()
    {

        $_SESSION['specification'] = $_POST['specification'];

    }


    function readFileResultInterpretTrace1()
    {


        $file_content = file('./outputs/output_interpret1');

        $string = explode('Casper>', $file_content[10]);


        $trace = trim($string[1]) . "<br>";


        $count = 11;

        while ($file_content[$count] != "\n") {

            $trace = $trace . trim($file_content[$count]) . "<br>";

            $count++;

        }

        return substr($trace, 0, -4);

    }

    function readFileResultInterpretFullTrace()
    {


        $fileContent = file('./outputs/output_interpret2');

        $string = explode('Casper>', $fileContent[10]);

        $trace = trim($string[1]) . "<br>";

        $count = 11;

        while ($fileContent[$count] != "\n") {

            $trace = $trace . trim($fileContent[$count]) . "<br>";
            $count++;

        }

        return substr($trace, 0, -4);

    }

}