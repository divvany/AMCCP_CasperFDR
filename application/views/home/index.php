<div class="content-wrapper">


    <section class="content-header">

        <h1>

            Casper & FDR


        </h1>

        <ol class="breadcrumb">

            <li><a href="<?= base_url(); ?>"><i class="fa fa-dashboard"></i> Home </a></li>

        </ol>

    </section>

    <section class="content">

        <div class="row">


            <div class="col-md-7">


                <div class="box box-primary">


                    <div class="box-header">
                        <h3 class="box-title"><span id="theWord">The</span> <label id="fileName"
                                                                                   class="fileNameSize"></label>
                            <span id="splWord">.spl file</span>
                            <small>Edit file</small>
                        </h3>


                        <button id="button" type="button" name="downFile" onclick="saveTextAsFile()"
                                class="btn btn-small btn-primary pull-right">
                            &nbsp; Save
                            this file &nbsp;&nbsp;
                        </button>


                    </div>

                    <!--                    --><?php //echo form_close(); ?>


                    <div class="box-body pad">

                        <div class="form-group">


                            <textarea id="textArea" name="fileContent" class="textAreaStyle" srequired
                                      placeholder="Usage:&#10; - Select a file from Casper library (or open your own custom file)&#10; - Edit the file as needed or write it directly here&#10; - Press 'Check protocol'"
                                      style="width: 100%; height:310px; font-size: 14px; line-height: 18px; border: 1px solid #dddddd; padding: 10px;"></textarea>


                        </div>

                    </div>

                    <div class="box-footer">


                        <button id="buttonCheckProtocol" name="checkProtocol" data-toggle="modal"
                                data-target="modal-default"
                                class="btn btn-primary btn-small pull-right" onclick="checkProtocol()">
                            Check
                            protocol
                        </button>


                        <input onchange="addTextFromFile()" id="myFile" type="file" name="fileLoaded"/>


                    </div>


                </div>
            </div>


            <div class="col-md-5">


                <div class="box box-primary">


                    <div class="box-header with-border">

                        <h3 class="box-title">Choose a file from Casper examples library:</h3>


                    </div>
                    <div class="box-body">


                        <div class="row">

                            <?php

                            function print_files($item, $key, $key_first)
                            {
                                if (!is_array($item)) {

                                    if ((strpos($item, '.spl') !== false) && (strpos($item, '~') == false)) {

                                        ?>
                                        <option onclick="addText('<?= $key_first; ?>','<?= $item; ?>');"
                                                value="<?= $key_first . $item; ?>"> <?= $item; ?></option>

                                        <?php

                                    }
                                } else {
                                    ?>
                                    <optgroup label="<?= substr($key, 0, -1); ?>">

                                        <!--                                        --><?php //array_walk_recursive($item, 'print_files',$key); ?>

                                        <?php
                                        foreach ($item as $file) {

                                            $folder = $key_first . $key;

                                            if ((strpos($file, '.spl') !== false) && (strpos($file, '~') == false)) {

                                                ?>
                                                <option onclick="addText('<?= $folder; ?>','<?= $file; ?>')"
                                                        value="<?= $folder . $file; ?>"> <?= $file; ?></option>

                                                <?php
                                            }

                                        }

                                        ?>
                                    </optgroup>

                                    <?php
                                }

                            }

                            foreach ($folders as $key => $item) {
                                ?>

                                <div class="col-md-6">


                                    <select name="filename" class="select_design">
                                        <option style="font-weight: bold" selected disabled
                                                value="<?= substr($key, 0, -1); ?>"><b> <?= substr($key, 0, -1); ?></b>
                                        </option>

                                        <?php
                                        asort($item);
                                        array_walk($item, 'print_files', $key);
                                        ?>

                                    </select>

                                </div>

                                <?php


                            }
                            ?>

                        </div>


                        <br>

                        <button class="btn btn-primary btn-block" onclick="checkProtocolFromLibrary()">Check protocol
                            from
                            library
                        </button>


                    </div>

                </div>


            </div>


        </div>


    </section>

</div>


<script type="text/javascript">

    var file_name = '';
    var file_path = '';
    var textArea = document.getElementById("textArea");
    var selectedFile = false;


    var file_n = 'file.spl';

    jQuery.ajax({
        type: "POST",
        data: {file_n: file_n},
        url: "<?php echo base_url() . "home/setFileName"; ?>"


    });

    function parseSyntax() {

        var dictionary = ["#Free variables", "#Processes", "#Protocol description", "#Specification", "#Equivalences", "#Actual variables", "#Functions", "#System", "#Intruder Information"];


        // will be completed


    }


    function getProtocolInfo(fileContent) {

        var protocolTokens = fileContent.split("#Free variables");

        var freeVariables = protocolTokens[1].split("#");


        var protocolVariables = freeVariables[0].trim();

        var tokens = protocolVariables.split("\n");

        var free_vars = "";

        for (i = 0; i < tokens.length; i++) {

            free_vars += tokens[i] + "*";

        }


        jQuery.ajax({
            type: "POST",
            data: {free_vars: free_vars},
            url: "<?php echo base_url() . "checkProtocol/getFreeVariables"; ?>"

        });


        protocolTokens = fileContent.split("#Actual variables");

        var actualVariables = protocolTokens[1].split("#");


        var protocolAgents = actualVariables[0].trim();

        tokens = protocolAgents.split("\n");

        var agents = "";

        for (i = 0; i < tokens.length; i++) {

            agents += tokens[i] + "*";

        }


        intruder = protocolTokens[1].split("#Intruder Information");

        intruderName = intruder[1].split("IntruderKnowledge");

        agents += "*";
        agents += intruderName[0].trim();


        jQuery.ajax({
            type: "POST",
            data: {agents: agents},
            url: "<?php echo base_url() . "checkProtocol/getActualVariables"; ?>"


        });


        protocolTokens = fileContent.split("#Protocol description");

        var protocolDescription = protocolTokens[1].split("#");


        var descLines = protocolDescription[0].trim();

        tokens = descLines.split('\n');

        var description = "";


        for (i = 0; i < tokens.length; i++) {

            description += tokens[i] + "*";

        }


        jQuery.ajax({
            type: "POST",
            data: {description: description},
            url: "<?php echo base_url() . "checkProtocol/getProtocolDescription"; ?>"


        });


        protocolTokens = fileContent.split("#Specification");

        var protocolSpecification = protocolTokens[1].split("#");


        var specLines = protocolSpecification[0].trim();

        tokens = specLines.split('\n');

        var specification = "";


        for (i = 0; i < tokens.length; i++) {

            if (tokens[i].includes("--") === false) {

                specification += tokens[i] + "*";
            }

        }


        jQuery.ajax({
            type: "POST",
            data: {specification: specification},
            url: "<?php echo base_url() . "checkProtocol/getProtocolSpecification"; ?>"


        });


    }

    function addText(folder, file) {


        path = "examples_library/";

        path += folder;
        path += file;
        file_name = file;

        $('#theWord').hide();
        $('#splWord').hide();

        $('#fileName').text(file);


        var rawFile = new XMLHttpRequest();
        rawFile.open("POST", path, true);
        rawFile.onreadystatechange = function () {
            if (rawFile.readyState === 4) {
                if (rawFile.status === 200 || rawFile.status == 0) {
                    var allText = rawFile.responseText;

                    textArea.value = allText;

                    getProtocolInfo(allText);

                }
            }
        }
        rawFile.send(null);


        var file_n = folder + file;
        file_path = file_n;

        jQuery.ajax({
            type: "POST",
            data: {file_n: file_n},
            url: "<?php echo base_url() . "home/setFileName"; ?>"


        });

        selectedFile = true;

    }


    function addTextFromFile() {


        $('#fileName').hide();
        $('#theWord').show();
        $('#splWord').show();
        var file = document.getElementById("myFile").files[0];


        var reader = new FileReader();
        reader.onload = function (e) {

            textArea.value = e.target.result;

        };
        reader.readAsText(file);

        file_name = file.name;


        var file_n = file_name;

        jQuery.ajax({
            type: "POST",
            data: {file_n: file_n},
            url: "<?php echo base_url() . "home/setFileName"; ?>"

            // ,
            // error: function (error) {
            //
            //     alert("error");
            //
            // },
            //
            // success: function (response) {
            //
            //     alert("succ");
            // }

        });

        $('#fileName').text(file_name);

        $('#theWord').hide();
        $('#splWord').hide();
        $('#fileName').show();

    }


    function saveTextAsFile() {

        var content = '';

        content = textArea.value;

        var filename = file_name;

        if (file_name === '') {
            filename = 'file.spl';
        }


        var textFileAsBlob = '';

        if (content != '') {

            textFileAsBlob = new Blob([content], {type: 'text/plain'});

            var downloadLink = document.createElement("a");
            downloadLink.download = filename;
            downloadLink.innerHTML = "Download File";
            if (window.webkitURL != null) {

                downloadLink.href = window.webkitURL.createObjectURL(textFileAsBlob);
            }
            else {

                downloadLink.href = window.URL.createObjectURL(textFileAsBlob);

                downloadLink.style.display = "none";
                document.body.appendChild(downloadLink);
            }

            //   downloadLink.click();
        }
        else {
            alert("The textarea is emthy!");
        }
    }


    function checkProtocol() {


        var fileContent = textArea.value;

        if (fileContent != false) {

            getProtocolInfo(fileContent);

            var fileName = file_path;


            jQuery.ajax({

                type: "POST",
                url: "<?php echo base_url() . "home/checkProtocol"; ?>",
                data: {fileName: fileName, fileContent: fileContent}


                // ,
                //
                // error: function (error) {
                //
                //     alert("error");
                //
                // },
                //
                // success: function (response) {
                //
                //     alert("succes");
                // }

            });


            window.location = "<?php echo base_url() . 'checkProtocol';?>";

        }

        else {

            alert("Text area is emthy!\nThere is no file selected!\nYou have to fill the textarea with a protocol description.\nYou can select it from the Casper library, upload it from your computer or write it directly in the text area!");
        }
    }

    function checkProtocolFromLibrary() {

        if (selectedFile) {


            var fileName = file_path;


            jQuery.ajax({

                type: "POST",
                url: "<?php echo base_url() . "home/checkProtocolFromLibrary"; ?>",
                data: {fileName: fileName}

                // ,
                //
                // error: function (error) {
                //
                //     alert("error");
                //
                // },
                //
                // success: function (response) {
                //
                //     alert("succes");
                // }

            });

            window.location = "<?php echo base_url() . 'checkProtocol';?>";
        }
        else {

            alert("There is no file selected!\nYou have to fill the textarea with a protocol description.\nYou can select it from the Casper library, upload it from your computer or write it directly in the text area!");

        }

    }


</script>
