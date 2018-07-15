<?php
defined('BASEPATH') OR exit('No direct script access allowed');

class Home extends CI_Controller
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


        $this->load->helper('directory');

        $map = directory_map('./examples_library/');

        ksort($map);

        $data["folders"] = $map;


        $this->load->view('home/index', $data);

        $this->load->view('includes/footer');


    }


    public function checkProtocolFromLibrary()
    {

        $path = './documents/' . $_POST['fileName'];

        $path = str_replace(".spl", ".csp", trim($path));

        $this->callFDRForJSON($path);

        $shellCommand = './lib_fdr ';

        $shellCommand = $shellCommand . $path;

        $shellCommand = $shellCommand . " > fdr_result";

        shell_exec($shellCommand)
        or die();


    }


    public function checkProtocol()
    {

        $this->load->helper('file');

        $data = trim($_POST['fileContent']);

        $fileContent = str_replace("\r", "", $data);


        $path = './documents/file.spl';


        if (!empty($fileContent)) {

            if (!write_file($path, $fileContent)) {
                $_SESSION['message_error'] = "Unable to write the .spl file!";
            }
        }

        @chmod($path, 0777);

        shell_exec('./casper_call');


        $path = './documents/file.csp';

        $this->callFDRForJSON($path);

        $shellCommand = './lib_fdr ';

        $shellCommand = $shellCommand . $path;

        $shellCommand = $shellCommand . " > fdr_result";

        shell_exec($shellCommand)

        or die();


    }


    public function callFDRForJSON($path)
    {

        $path = str_replace(".spl", ".csp", trim($path));

        $cmdString = 'refines --quiet --format json ';

        $cmdString = $cmdString . $path;

        $cmdString = $cmdString . " > json_fdr.json";

        shell_exec($cmdString);

    }

    public function setFileName()
    {

        $_SESSION['fileName'] = $_POST['file_n'];

    }

}
